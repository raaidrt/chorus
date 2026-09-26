# Per-move benchmarks

`benches/per_move.rs` measures what one move costs the engine: the verified primitives on
reference positions and on real games, and the full per-move pipeline ply by ply along
whole games. `benches/codspeed.rs` runs the same workloads under
[CodSpeed](https://codspeed.io) in CI (see [below](#codspeed)). Both share
`benches/common/mod.rs`.

```sh
cargo bench --bench per_move                     # full run (~1 min), writes target/bench/per_move.json
cargo bench --bench per_move -- --quick          # ~10 s smoke run
cargo bench --bench per_move -- --filter kiwipete
python3 scripts/bench_report.py target/bench/per_move.json > report.md
```

Options: `--samples N` (default 30), `--sample-ms MS` (minimum time per sample, default 2),
`--filter SUBSTR`, `--seed N` (round order and bootstrap), `--out PATH`.

## What is measured

| Benchmark | Unit | What it times |
|---|---|---|
| `legal_moves/<pos>` | call | `legal_moves_exec` |
| `is_legal/<pos>` | move | `is_legal_exec`, averaged over every legal move of `<pos>` |
| `apply_move/<pos>` | move | `apply_move_exec`, averaged over every legal move of `<pos>` |
| `outcome/<pos>` | call | `Game::outcome` (mate, stalemate, draw detection) |
| `lichess/legal_moves` | position | `legal_moves_exec` on every position of the Lichess sample |
| `lichess/is_legal` | move | `is_legal_exec` on every legal move of those positions |
| `lichess/apply_move` | move | `apply_move_exec` on every legal move of those positions |
| `lichess/replay` | move | every game replayed from the start: `legal_moves` + `play` + `outcome` at each ply |
| `ply/<game>/legal_moves/<k>` | move | move generation before the `k`-th move |
| `ply/<game>/play/<k>` | move | `Game::play` of the `k`-th move |
| `ply/<game>/outcome/<k>` | move | `Game::outcome` after the `k`-th move |
| `ply/<game>/step/<k>` | move | all three in sequence, i.e. the engine's full cost of that move |

Positions are the perft references from `tests/perft.rs`; their legal move counts are
asserted before timing. `play` and `step` undo the move with `history.pop()`, which costs
a few ns and is included, instead of cloning the whole history each iteration.

### Game data

The games are 100 real Lichess games (7,176 plies, 7,276 positions) in
`benches/data/lichess_games.txt`. They were sampled with a fixed seed from the
[Chess Game Dataset (Lichess)](https://www.kaggle.com/datasets/datasnaek/chess)
(CC0: Public Domain): 51 resignations, 36 mates, 7 draws and 6 losses on time, from 11 to
208 plies. `scripts/lichess_games.py` regenerates the file and documents the sampling; it
converts the dataset's SAN to UCI with python-chess. When the benchmarks start, they
replay every game with `Game::play` and check that games recorded as mate end in
checkmate, so a transcription error fails instead of timing a truncated game.

The per-ply benchmarks (`ply/<game>/…`) cover two of these games: `ILZ77Y8B` (65 plies,
the median length, ends in mate) and `jGiADcVr` (135 plies, drawn after a long endgame).

## Methodology

* **Batching.** Each sample times as many iterations as it takes to fill the minimum sample
  time, found by doubling. Clock overhead and resolution (logged at startup) are then
  negligible, and the doubling also warms caches and branch predictors.
* **CPU warm-up** before measuring, so frequency scaling has settled.
* **Interleaved rounds.** Every round takes one sample of every benchmark in a freshly
  shuffled order. Drift over the run (thermal throttling, noisy neighbours) then
  spreads evenly across benchmarks instead of landing on whichever ran at a bad moment.
* **`std::hint::black_box`** on inputs and outputs of every iteration.
* **Deterministic workloads**: fixed positions and a fixed sample of real games.
* **Robust statistics.** Medians with 95% bootstrap confidence intervals. Outliers are
  counted (Tukey's fences) but kept, since they can be real (allocation, preemption).
  All raw samples are written to the JSON.
* **Build**: the `bench` profile adds `codegen-units = 1` to the release settings, so that
  unrelated edits do not reshuffle code layout.
* **Environment capture**: commit, dirty flag, rustc, CPU, governor and load average are
  recorded with every result.

## Comparing two versions

**Use several processes per side, interleaved.** Heap placement and code layout change
from one process to the next and can move a benchmark by several percent. In an A/A
test (identical binaries), `Game::play` at ≈80 ns ran 8% slower in one of two processes
on every ply, while the samples inside each process were tight. More samples per
process can't expose that; more processes can. Build both versions first, then
alternate between them so machine drift affects both sides equally. A git worktree
keeps the baseline in its own checkout, so each run records the right commit:

```sh
git worktree add ../base main
out=$PWD/target/bench && mkdir -p "$out"
(cd ../base && cargo bench --bench per_move --no-run) && cargo bench --bench per_move --no-run
for i in 1 2 3; do
  (cd ../base && cargo bench -q --bench per_move -- --out "$out/base-$i.json")
  cargo bench -q --bench per_move -- --out "$out/new-$i.json"
done
python3 scripts/bench_report.py "$out"/new-*.json --baseline "$out"/base-*.json > report.md
```

The report pools the runs and uses a hierarchical bootstrap (resample runs, then samples within each
run) for all confidence intervals. It flags a change only when the 95% CI of the ratio
of medians lies entirely beyond `--threshold` (default ±3%). The output is GitHub
Markdown with Mermaid charts, so it can go straight into a PR description or comment.

For quieter numbers: close other workloads, pin to one core (`taskset -c 2 ...`), use
the `performance` governor, and disable turbo if you can. Before trusting a small change
on a new machine, run an A/A comparison (the same binary on both sides) to see how
large a change that machine flags by pure noise.

## CodSpeed

`.github/workflows/codspeed.yml` runs `benches/codspeed.rs` on every push to `main` and on
every pull request, using [CodSpeed](https://codspeed.io)'s simulation mode. Simulation
counts instructions and simulates the cache, so results are stable on shared CI runners.
CodSpeed keeps the history for `main` and comments on each pull request with the changes.
The benchmarks are written for divan (via `codspeed-divan-compat`), which CodSpeed
instruments:

| Benchmark | What it times |
|---|---|
| `reference::{legal_moves,has_legal_move,is_legal,apply_move,outcome}[<pos>]` | the primitives on each perft position (`is_legal`/`apply_move`: all its legal moves) |
| `lichess::{legal_moves,is_legal,apply_move}` | the same primitives swept over every position of the Lichess sample |
| `lichess::replay_all` | all 100 games replayed from the start |
| `lichess::replay_game[<id>]` | one game replayed from the start |

```sh
cargo bench --bench codspeed                  # plain divan wall-time run, locally
cargo install cargo-codspeed --locked
cargo codspeed build --bench codspeed && cargo codspeed run --bench codspeed   # as in CI
```

Outside the CodSpeed runner, `cargo codspeed run` only checks that every benchmark runs.
Use `per_move.rs` for per-ply numbers and wall-time A/B comparisons.
