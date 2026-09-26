# Per-move benchmarks

`benches/per_move.rs` measures what one move costs the engine: the verified primitives on
reference positions, and the full per-move pipeline ply by ply along whole games.

```sh
cargo bench --bench per_move                     # full run (~1 min), writes target/bench/per_move.json
cargo bench --bench per_move -- --quick          # ~10 s smoke run
cargo bench --bench per_move -- --filter kiwipete
python3 scripts/bench_report.py target/bench/per_move.json > report.md
```

Options: `--samples N` (default 30), `--sample-ms MS` (minimum time per sample, default 2),
`--filter SUBSTR`, `--seed N` (random game), `--out PATH`.

## What is measured

| Benchmark | Unit | What it times |
|---|---|---|
| `legal_moves/<pos>` | call | `legal_moves_exec` |
| `is_legal/<pos>` | move | `is_legal_exec`, averaged over every legal move of `<pos>` |
| `apply_move/<pos>` | move | `apply_move_exec`, averaged over every legal move of `<pos>` |
| `outcome/<pos>` | call | `Game::outcome` (mate, stalemate, draw detection) |
| `ply/<game>/legal_moves/<k>` | move | move generation before the `k`-th move |
| `ply/<game>/play/<k>` | move | `Game::play` of the `k`-th move |
| `ply/<game>/outcome/<k>` | move | `Game::outcome` after the `k`-th move |
| `ply/<game>/step/<k>` | move | all three in sequence, i.e. the engine's full cost of that move |

Positions are the perft references from `tests/perft.rs`; their legal move counts are
asserted before timing. The games are the 1858 "Opera Game" (33 plies, ends in mate) and
a seeded random game (120 plies). `play` and `step` undo the move with `history.pop()`,
which costs a few ns and is included, instead of cloning the whole history each iteration.

## Methodology

* **Batching.** Each sample times as many iterations as it takes to fill the minimum sample
  time, found by doubling. Clock overhead and resolution (logged at startup) are then
  negligible, and the doubling also warms caches and branch predictors.
* **CPU warm-up** before measuring, so frequency scaling has settled.
* **Interleaved rounds.** Every round takes one sample of every benchmark in a freshly
  shuffled order. Drift over the run (thermal throttling, noisy neighbours) then
  spreads evenly across benchmarks instead of landing on whichever ran at a bad moment.
* **`std::hint::black_box`** on inputs and outputs of every iteration.
* **Deterministic workloads**: fixed positions, a fixed game and a seeded random game.
* **Robust statistics.** Medians with 95% bootstrap confidence intervals. Outliers are
  counted (Tukey's fences) but kept, since they can be real (allocation, preemption).
  All raw samples are written to the JSON.
* **Build**: the `bench` profile adds `codegen-units = 1` to the release settings, so that
  unrelated edits do not reshuffle code layout.
* **Environment capture**: commit, dirty flag, rustc, CPU, governor and load average are
  recorded with every result.

## Comparing two versions

Run both versions on the same machine, back to back, and compare:

```sh
git checkout main       && cargo bench --bench per_move -- --out target/bench/base.json
git checkout my-branch  && cargo bench --bench per_move -- --out target/bench/new.json
python3 scripts/bench_report.py target/bench/new.json --baseline target/bench/base.json > report.md
```

A change is flagged only when the bootstrap 95% CI of the ratio of medians lies entirely
beyond `--threshold` (default ±3%). The report is GitHub Markdown with Mermaid charts,
so it can be pasted straight into a PR description or comment.

For quieter numbers: close other workloads, pin to one core (`taskset -c 2 cargo bench ...`),
use the `performance` governor, and disable turbo if you can. On shared or virtual
machines, expect 1–2% drift between separate runs even of identical code. Two
identical runs on a 2-vCPU cloud VM flagged 8 of 636 benchmarks, all under 5%.
Treat smaller changes as noise unless they reproduce.
