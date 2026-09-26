//! Per-move timing harness.
//!
//! Measures what one move costs the engine, both on a fixed corpus of positions and
//! ply by ply along whole games:
//!
//! * `legal_moves/<pos>` — `legal_moves_exec` (per call, and per generated move)
//! * `is_legal/<pos>`    — `is_legal_exec` on every legal move (per move)
//! * `apply_move/<pos>`  — `apply_move_exec` on every legal move (per move)
//! * `outcome/<pos>`     — `Game::outcome` (mate/stalemate/draw detection)
//! * `ply/<game>/<component>/<k>` — at ply `k` of a game: `legal_moves`, `play`
//!   (`Game::play`), `outcome` (on the resulting game) and `step`, all three in sequence.
//!
//! Run with `cargo bench --bench per_move -- [options]`, and see `benches/README.md` for
//! the methodology. Results go to `target/bench/per_move.json`, which
//! `scripts/bench_report.py` turns into a Markdown report (tables and charts).
use chess_engine::fen::{move_to_uci, parse_fen, parse_uci_move};
use chess_engine::game::Game;
use chess_engine::movegen::{apply_move_exec, is_legal_exec, legal_moves_exec};
use chess_engine::position::Position;
use chess_engine::types::Move;
use std::fmt::Write as _;
use std::io::IsTerminal;
use std::hint::black_box;
use std::time::{Duration, Instant};

// ---------------------------------------------------------------------------
// Workloads
// ---------------------------------------------------------------------------

/// Perft reference positions (see `tests/perft.rs`) with their known move counts, so a
/// benchmark can never silently time the wrong thing.
const POSITIONS: &[(&str, &str, usize)] = &[
    ("start", "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", 20),
    ("kiwipete", "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", 48),
    ("pos3_endgame", "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 14),
    ("pos4_promotions", "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", 6),
    ("pos5", "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8", 44),
    ("pos6_middlegame", "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10", 46),
];

/// Morphy vs. Duke Karl / Count Isouard, Paris 1858 (the "Opera Game"), ending in mate.
const OPERA_GAME: &str = "e2e4 e7e5 g1f3 d7d6 d2d4 c8g4 d4e5 g4f3 d1f3 d6e5 f1c4 g8f6 f3b3 d8e7 \
     b1c3 c7c6 c1g5 b7b5 c3b5 c6b5 c4b5 b8d7 e1c1 a8d8 d1d7 d8d7 h1d1 e7e6 b5d7 f6d7 b3b8 d7b8 d1d8";

/// Plies in the seeded random game (it stops earlier if the game ends).
const RANDOM_GAME_PLIES: usize = 120;

/// xorshift64*: a tiny deterministic PRNG, so every run times the same workload.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn opera_game() -> Vec<Move> {
    OPERA_GAME.split_whitespace().map(|s| parse_uci_move(s).expect("bad UCI move")).collect()
}

fn random_game(seed: u64) -> Vec<Move> {
    let mut rng = Rng(seed | 1);
    let mut g = Game::new();
    let mut moves = Vec::new();
    while moves.len() < RANDOM_GAME_PLIES && g.outcome().is_none() {
        let legal = legal_moves_exec(g.current());
        let m = legal[rng.below(legal.len())];
        assert!(g.play(m));
        moves.push(m);
    }
    moves
}

/// Every prefix of a game: `states[k]` is the game after `k` plies.
fn game_states(moves: &[Move]) -> Vec<Game> {
    let mut g = Game::new();
    let mut states = vec![clone_game(&g)];
    for (k, &m) in moves.iter().enumerate() {
        assert!(g.play(m), "illegal move {} at ply {k}", move_to_uci(m));
        states.push(clone_game(&g));
    }
    states
}

fn clone_game(g: &Game) -> Game {
    Game { history: g.history.clone() }
}

// ---------------------------------------------------------------------------
// Benchmarks
// ---------------------------------------------------------------------------

/// One benchmark: `run(n)` executes the routine `n` times and returns the elapsed time.
/// Only the routine is inside the timed region; each `run` does its own untimed setup.
struct Bench {
    id: String,
    /// Units of work per iteration (e.g. the number of moves swept), so results can be
    /// reported per move rather than per sweep.
    units_per_iter: usize,
    unit: &'static str,
    /// Extra fields copied into the JSON output (`"key": value`).
    extra: Vec<(&'static str, String)>,
    run: Box<dyn FnMut(u64) -> Duration>,
}

/// Times `n` calls of `f` on `input`. The input goes through `black_box` on every
/// iteration, so the call cannot be hoisted out of the loop, and so does the output, so
/// it cannot be optimized away.
fn timed<I, O>(n: u64, input: &I, mut f: impl FnMut(&I) -> O) -> Duration {
    let start = Instant::now();
    for _ in 0..n {
        black_box(f(black_box(input)));
    }
    start.elapsed()
}

fn corpus_benches(out: &mut Vec<Bench>) {
    for &(name, fen, expected) in POSITIONS {
        let pos = parse_fen(fen).unwrap();
        let moves = legal_moves_exec(&pos);
        assert_eq!(moves.len(), expected, "legal move count of {name}");
        let n = moves.len();
        let extra = vec![("position", format!("\"{name}\"")), ("moves", n.to_string())];

        out.push(Bench {
            id: format!("legal_moves/{name}"),
            units_per_iter: 1,
            unit: "call",
            extra: extra.clone(),
            run: Box::new(move |iters| timed(iters, &pos, legal_moves_exec)),
        });
        let ms = moves.clone();
        out.push(Bench {
            id: format!("is_legal/{name}"),
            units_per_iter: n,
            unit: "move",
            extra: extra.clone(),
            run: Box::new(move |iters| {
                timed(iters, &pos, |p| ms.iter().filter(|&&m| is_legal_exec(p, black_box(m))).count())
            }),
        });
        let ms = moves.clone();
        out.push(Bench {
            id: format!("apply_move/{name}"),
            units_per_iter: n,
            unit: "move",
            extra: extra.clone(),
            run: Box::new(move |iters| {
                timed(iters, &pos, |p| {
                    for &m in &ms {
                        black_box(apply_move_exec(p, black_box(m)));
                    }
                })
            }),
        });
        let g = Game::from_position(pos);
        out.push(Bench {
            id: format!("outcome/{name}"),
            units_per_iter: 1,
            unit: "call",
            extra,
            run: Box::new(move |iters| timed(iters, &g, |g| g.outcome())),
        });
    }
}

/// Per-ply benchmarks along a game. At ply `k` (the `k`-th move, from the game after `k`
/// plies): `legal_moves` for the side to move, `play` of the game's move, `outcome` of the
/// resulting game, and `step` = all three in sequence, i.e. the engine's cost of one move.
///
/// `play` and `step` mutate the game, so they undo the move with `history.pop()` (a few
/// ns, included in the timing) instead of cloning the whole history per iteration.
fn game_benches(game: &str, moves: &[Move], out: &mut Vec<Bench>) {
    let states = game_states(moves);
    for (k, &m) in moves.iter().enumerate() {
        let extra = vec![
            ("game", format!("\"{game}\"")),
            ("ply", (k + 1).to_string()),
            ("move", format!("\"{}\"", move_to_uci(m))),
            ("moves", legal_moves_exec(states[k].current()).len().to_string()),
        ];
        let mut push = |component: &str, run: Box<dyn FnMut(u64) -> Duration>| {
            let mut extra = extra.clone();
            extra.push(("component", format!("\"{component}\"")));
            out.push(Bench {
                id: format!("ply/{game}/{component}/{:03}", k + 1),
                units_per_iter: 1,
                unit: "move",
                extra,
                run,
            });
        };

        let pos = *states[k].current();
        push("legal_moves", Box::new(move |iters| timed(iters, &pos, legal_moves_exec)));

        let mut g = clone_game(&states[k]);
        push(
            "play",
            Box::new(move |iters| {
                let start = Instant::now();
                for _ in 0..iters {
                    assert!(black_box(&mut g).play(black_box(m)));
                    g.history.pop();
                }
                start.elapsed()
            }),
        );

        let after = clone_game(&states[k + 1]);
        push("outcome", Box::new(move |iters| timed(iters, &after, |g| g.outcome())));

        let mut g = clone_game(&states[k]);
        push(
            "step",
            Box::new(move |iters| {
                let start = Instant::now();
                for _ in 0..iters {
                    let g = black_box(&mut g);
                    black_box(legal_moves_exec(g.current()));
                    assert!(g.play(black_box(m)));
                    black_box(g.outcome());
                    g.history.pop();
                }
                start.elapsed()
            }),
        );
    }
}

// ---------------------------------------------------------------------------
// Measurement
// ---------------------------------------------------------------------------

struct Config {
    samples: usize,
    /// Minimum duration of one timed sample; iterations are batched until it is reached,
    /// so timer resolution and overhead are negligible.
    sample_target: Duration,
    warmup: Duration,
    filter: Option<String>,
    seed: u64,
    out: String,
}

impl Config {
    fn from_args() -> Config {
        let mut c = Config {
            samples: 30,
            sample_target: Duration::from_millis(2),
            warmup: Duration::from_secs(1),
            filter: None,
            seed: 0x5eed,
            out: "target/bench/per_move.json".into(),
        };
        let mut args = std::env::args().skip(1);
        while let Some(a) = args.next() {
            let mut val = || args.next().unwrap_or_else(|| panic!("{a} needs a value"));
            match a.as_str() {
                "--quick" => {
                    c.samples = 10;
                    c.sample_target = Duration::from_millis(1);
                    c.warmup = Duration::from_millis(300);
                }
                "--samples" => c.samples = val().parse().expect("--samples N"),
                "--sample-ms" => c.sample_target = Duration::from_secs_f64(val().parse::<f64>().expect("--sample-ms MS") / 1e3),
                "--filter" => c.filter = Some(val()),
                "--seed" => c.seed = val().parse().expect("--seed N"),
                "--out" => c.out = val(),
                // Passed by `cargo bench`.
                "--bench" => {}
                "-h" | "--help" => {
                    println!(
                        "options: --quick | --samples N | --sample-ms MS | --filter SUBSTR | --seed N | --out PATH"
                    );
                    std::process::exit(0);
                }
                other => panic!("unknown argument {other} (try --help)"),
            }
        }
        assert!(c.samples >= 5, "need at least 5 samples");
        c
    }
}

/// Smallest `n` (a power of two) such that `run(n)` takes at least `target`. The
/// repeated doubling also warms the routine up (caches, branch predictors).
fn calibrate(b: &mut Bench, target: Duration) -> u64 {
    let mut n = 1u64;
    loop {
        if (b.run)(n) >= target || n >= 1 << 40 {
            return n;
        }
        n *= 2;
    }
}

/// Burns CPU so frequency scaling and turbo states settle before anything is measured.
fn warm_up_cpu(d: Duration) {
    let start = Instant::now();
    let pos = Position::initial();
    while start.elapsed() < d {
        black_box(legal_moves_exec(black_box(&pos)));
    }
}

/// Median overhead of reading the clock twice, and the smallest nonzero step it reports.
fn timer_precision() -> (f64, f64) {
    let mut deltas: Vec<f64> = (0..10_000)
        .map(|_| {
            let a = Instant::now();
            let b = Instant::now();
            (b - a).as_nanos() as f64
        })
        .collect();
    deltas.sort_by(f64::total_cmp);
    let resolution = deltas.iter().copied().find(|&d| d > 0.0).unwrap_or(0.0);
    (deltas[deltas.len() / 2], resolution)
}

struct Stats {
    median: f64,
    mean: f64,
    stddev: f64,
    mad: f64,
    min: f64,
    max: f64,
    p05: f64,
    p95: f64,
    ci_lo: f64,
    ci_hi: f64,
    mild_outliers: usize,
    severe_outliers: usize,
}

fn quantile(sorted: &[f64], q: f64) -> f64 {
    let pos = q * (sorted.len() - 1) as f64;
    let (lo, hi) = (pos.floor() as usize, pos.ceil() as usize);
    sorted[lo] + (sorted[hi] - sorted[lo]) * (pos - lo as f64)
}

fn median(xs: &mut [f64]) -> f64 {
    xs.sort_by(f64::total_cmp);
    quantile(xs, 0.5)
}

/// Summary statistics. The 95% confidence interval of the median is a percentile
/// bootstrap (2000 resamples); outliers are counted with Tukey's fences but kept, since
/// dropping them would hide real effects such as allocation or preemption.
fn stats(samples: &[f64], rng: &mut Rng) -> Stats {
    let mut s = samples.to_vec();
    s.sort_by(f64::total_cmp);
    let n = s.len() as f64;
    let mean = s.iter().sum::<f64>() / n;
    let stddev = (s.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / (n - 1.0)).sqrt();
    let med = quantile(&s, 0.5);
    let mad = median(&mut s.iter().map(|x| (x - med).abs()).collect::<Vec<_>>());
    let (q1, q3) = (quantile(&s, 0.25), quantile(&s, 0.75));
    let iqr = q3 - q1;
    let outside = |k: f64| s.iter().filter(|&&x| x < q1 - k * iqr || x > q3 + k * iqr).count();
    let severe = outside(3.0);

    let mut boot: Vec<f64> = (0..2000)
        .map(|_| median(&mut (0..s.len()).map(|_| s[rng.below(s.len())]).collect::<Vec<_>>()))
        .collect();
    boot.sort_by(f64::total_cmp);

    Stats {
        median: med,
        mean,
        stddev,
        mad,
        min: s[0],
        max: s[s.len() - 1],
        p05: quantile(&s, 0.05),
        p95: quantile(&s, 0.95),
        ci_lo: quantile(&boot, 0.025),
        ci_hi: quantile(&boot, 0.975),
        mild_outliers: outside(1.5) - severe,
        severe_outliers: severe,
    }
}

// ---------------------------------------------------------------------------
// Environment and output
// ---------------------------------------------------------------------------

fn command_output(cmd: &str, args: &[&str]) -> String {
    std::process::Command::new(cmd)
        .args(args)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".into())
}

fn read_trimmed(path: &str) -> String {
    std::fs::read_to_string(path).map(|s| s.trim().to_string()).unwrap_or_else(|_| "unknown".into())
}

fn json_str(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => write!(out, "\\u{:04x}", c as u32).unwrap(),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn environment(cfg: &Config, timer: (f64, f64)) -> Vec<(&'static str, String)> {
    let cpu = std::fs::read_to_string("/proc/cpuinfo")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("model name")).map(|l| l.split(':').nth(1).unwrap().trim().to_string()))
        .unwrap_or_else(|| "unknown".into());
    let dirty = !command_output("git", &["status", "--porcelain", "--untracked-files=no"]).is_empty();
    vec![
        ("git_commit", json_str(&command_output("git", &["rev-parse", "HEAD"]))),
        ("git_branch", json_str(&command_output("git", &["rev-parse", "--abbrev-ref", "HEAD"]))),
        ("git_dirty", dirty.to_string()),
        ("rustc", json_str(&command_output("rustc", &["-V"]))),
        ("debug_assertions", cfg!(debug_assertions).to_string()),
        ("cpu", json_str(&cpu)),
        ("logical_cpus", std::thread::available_parallelism().map_or(0, |n| n.get()).to_string()),
        ("governor", json_str(&read_trimmed("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor"))),
        ("loadavg", json_str(&read_trimmed("/proc/loadavg"))),
        ("kernel", json_str(&command_output("uname", &["-sr"]))),
        ("timestamp_unix", std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs().to_string()),
        ("timer_overhead_ns", format!("{:.1}", timer.0)),
        ("timer_resolution_ns", format!("{:.1}", timer.1)),
        ("samples", cfg.samples.to_string()),
        ("sample_target_ms", format!("{}", cfg.sample_target.as_secs_f64() * 1e3)),
        ("warmup_ms", cfg.warmup.as_millis().to_string()),
        ("seed", cfg.seed.to_string()),
    ]
}

fn human(ns: f64) -> String {
    match ns {
        x if x < 1e3 => format!("{x:.1} ns"),
        x if x < 1e6 => format!("{:.2} µs", x / 1e3),
        x => format!("{:.2} ms", x / 1e6),
    }
}

fn main() {
    let cfg = Config::from_args();
    if cfg!(debug_assertions) {
        eprintln!("warning: debug assertions are on; numbers will not be representative");
    }

    let mut benches = Vec::new();
    corpus_benches(&mut benches);
    game_benches("opera", &opera_game(), &mut benches);
    game_benches("random", &random_game(cfg.seed), &mut benches);
    if let Some(f) = &cfg.filter {
        benches.retain(|b| b.id.contains(f.as_str()));
    }
    assert!(!benches.is_empty(), "no benchmark matches the filter");

    let timer = timer_precision();
    eprintln!(
        "{} benchmarks x {} samples; timer overhead {:.0} ns, resolution {:.0} ns",
        benches.len(),
        cfg.samples,
        timer.0,
        timer.1
    );
    warm_up_cpu(cfg.warmup);

    let started = Instant::now();
    let iters: Vec<u64> = benches.iter_mut().map(|b| calibrate(b, cfg.sample_target)).collect();

    // Interleave: each round takes one sample of every benchmark, in a fresh random
    // order. Slow drift (thermal throttling, noisy neighbours) then spreads evenly over
    // all benchmarks instead of biasing whichever ran during a bad stretch.
    let mut rng = Rng(cfg.seed ^ 0x9e37_79b9_7f4a_7c15);
    let mut samples = vec![Vec::with_capacity(cfg.samples); benches.len()];
    let mut order: Vec<usize> = (0..benches.len()).collect();
    let progress = std::io::stderr().is_terminal();
    for round in 0..cfg.samples {
        for i in (1..order.len()).rev() {
            order.swap(i, rng.below(i + 1));
        }
        for &i in &order {
            let d = (benches[i].run)(iters[i]);
            samples[i].push(d.as_nanos() as f64 / iters[i] as f64);
        }
        if progress {
            eprint!("\rround {}/{}", round + 1, cfg.samples);
        }
    }
    eprintln!("{}measured in {:.1} s", if progress { "\r" } else { "" }, started.elapsed().as_secs_f64());

    let mut json = String::from("{\n  \"schema\": 1,\n  \"environment\": {\n");
    let env = environment(&cfg, timer);
    for (i, (k, v)) in env.iter().enumerate() {
        writeln!(json, "    \"{k}\": {v}{}", if i + 1 < env.len() { "," } else { "" }).unwrap();
    }
    json.push_str("  },\n  \"benchmarks\": [\n");
    println!("{:<34} {:>16} {:>24} {:>7} {:>9}", "benchmark", "median", "95% CI", "CV", "outliers");
    for (i, b) in benches.iter().enumerate() {
        let s = stats(&samples[i], &mut rng);
        if !b.id.starts_with("ply/") || cfg.filter.is_some() {
            let u = b.units_per_iter as f64;
            println!(
                "{:<34} {:>16} {:>24} {:>6.1}% {:>9}",
                b.id,
                format!("{}/{}", human(s.median / u), b.unit),
                format!("[{}, {}]", human(s.ci_lo / u), human(s.ci_hi / u)),
                100.0 * s.stddev / s.mean,
                s.mild_outliers + s.severe_outliers
            );
        }
        let per_iter: Vec<String> = samples[i].iter().map(|x| format!("{x:.3}")).collect();
        write!(
            json,
            "    {{\"id\": {}, \"unit\": \"{}\", \"units_per_iter\": {}, \"iters_per_sample\": {}, \
             \"median_ns\": {:.3}, \"mean_ns\": {:.3}, \"stddev_ns\": {:.3}, \"mad_ns\": {:.3}, \
             \"min_ns\": {:.3}, \"max_ns\": {:.3}, \"p05_ns\": {:.3}, \"p95_ns\": {:.3}, \
             \"ci95_ns\": [{:.3}, {:.3}], \"outliers\": {{\"mild\": {}, \"severe\": {}}}",
            json_str(&b.id),
            b.unit,
            b.units_per_iter,
            iters[i],
            s.median,
            s.mean,
            s.stddev,
            s.mad,
            s.min,
            s.max,
            s.p05,
            s.p95,
            s.ci_lo,
            s.ci_hi,
            s.mild_outliers,
            s.severe_outliers
        )
        .unwrap();
        for (k, v) in &b.extra {
            write!(json, ", \"{k}\": {v}").unwrap();
        }
        write!(json, ", \"samples_ns\": [{}]}}", per_iter.join(", ")).unwrap();
        json.push_str(if i + 1 < benches.len() { ",\n" } else { "\n" });
    }
    json.push_str("  ]\n}\n");

    if let Some(dir) = std::path::Path::new(&cfg.out).parent() {
        std::fs::create_dir_all(dir).unwrap();
    }
    std::fs::write(&cfg.out, json).unwrap();
    eprintln!("wrote {} (per-ply results are only in the JSON)", cfg.out);
}
