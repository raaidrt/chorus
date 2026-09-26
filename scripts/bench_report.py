#!/usr/bin/env python3
"""Turn `benches/per_move.rs` output into a Markdown report (GitHub-flavoured).

    python3 scripts/bench_report.py new-*.json [--baseline base-*.json] > report.md

Tables and Mermaid `xychart-beta` charts render inline in GitHub PR descriptions,
comments and job summaries.

Pass several JSON files (separate `cargo bench` invocations) per side: code layout and
heap placement differ between processes and can shift a benchmark by several percent,
which no amount of samples within one process reveals. Confidence intervals are then a
hierarchical bootstrap (resample runs, then samples within each run).

With `--baseline`, every benchmark is compared with a bootstrap confidence interval of
the ratio of medians; a change is flagged only if that interval lies entirely beyond
`--threshold` percent. Standard library only.
"""
import argparse
import json
import random
import statistics
import sys
from datetime import datetime, timezone

# Categorical slots 1-3 of the reference palette (blue, orange, aqua), with the
# matching emoji swatches, since xychart-beta has no legend of its own.
PALETTE = ["#2a78d6", "#eb6834", "#1baf7a"]
SWATCH = ["🟦", "🟧", "🟩"]
COMPONENTS = ["legal_moves", "play", "outcome"]


def fmt_ns(ns):
    if ns < 1e3:
        return f"{ns:.1f} ns"
    if ns < 1e6:
        return f"{ns / 1e3:.2f} µs"
    return f"{ns / 1e6:.2f} ms"


def per_unit(b, key="median_ns"):
    return b[key] / b["units_per_iter"]


def with_ci(b):
    """Median per unit, with the 95% CI half-width as a percentage."""
    lo, hi = b["ci95_ns"]
    return f"{fmt_ns(per_unit(b))} <sub>±{50 * (hi - lo) / b['median_ns']:.1f}%</sub>"


def load(path):
    with open(path) as f:
        data = json.load(f)
    if data.get("schema") != 1:
        sys.exit(f"{path}: unsupported schema {data.get('schema')}")
    return data


def ply_series(benches, game, component):
    rows = [b for b in benches if b["id"].startswith(f"ply/{game}/{component}/")]
    return sorted(rows, key=lambda b: b["ply"])


def games(benches):
    return list(dict.fromkeys(b["game"] for b in benches if b["id"].startswith("ply/")))


def xychart(title, x_label, y_label, series, x_values=None):
    """A Mermaid line chart; `series` is a list of lists of y values."""
    n = len(series[0])
    palette = ", ".join(PALETTE[: len(series)])
    lines = [
        "```mermaid",
        '%%{init: {"themeVariables": {"xyChart": {"plotColorPalette": "' + palette + '"}}}}%%',
        "xychart-beta",
        f'    title "{title}"',
        f'    x-axis "{x_label}" 1 --> {n}' if x_values is None else f"    x-axis [{', '.join(x_values)}]",
        f'    y-axis "{y_label}"',
    ]
    for ys in series:
        lines.append(f"    line [{', '.join(f'{y:.2f}' for y in ys)}]")
    lines.append("```")
    return "\n".join(lines)


def barchart(title, labels, y_label, values):
    return "\n".join(
        [
            "```mermaid",
            '%%{init: {"themeVariables": {"xyChart": {"plotColorPalette": "' + PALETTE[0] + '"}}}}%%',
            "xychart-beta",
            f'    title "{title}"',
            f"    x-axis [{', '.join(labels)}]",
            f'    y-axis "{y_label}" 0 --> {max(values) * 1.15:.1f}',
            f"    bar [{', '.join(f'{v:.2f}' for v in values)}]",
            "```",
        ]
    )


# ---------------------------------------------------------------------------
# Sections
# ---------------------------------------------------------------------------


def corpus_section(benches):
    by_id = {b["id"]: b for b in benches}
    positions = [b["position"] for b in benches if b["id"].startswith("legal_moves/")]
    if not positions:
        return ""
    out = [
        "### Cost per move on reference positions",
        "",
        "Median time, ± half-width of its 95% bootstrap CI. `legal_moves` and `outcome` are per call; "
        "the others are per move, averaged over every legal move of the position.",
        "",
        "| Position | Legal moves | `legal_moves_exec` | … per generated move | `is_legal_exec` / move "
        "| `apply_move_exec` / move | `Game::outcome` |",
        "|---|--:|--:|--:|--:|--:|--:|",
    ]
    for p in positions:
        lm = by_id[f"legal_moves/{p}"]
        out.append(
            f"| `{p}` | {lm['moves']} | {with_ci(lm)} | {fmt_ns(lm['median_ns'] / lm['moves'])} "
            f"| {with_ci(by_id[f'is_legal/{p}'])} | {with_ci(by_id[f'apply_move/{p}'])} "
            f"| {with_ci(by_id[f'outcome/{p}'])} |"
        )
    out += [
        "",
        barchart(
            "legal_moves_exec per call (µs)",
            [p.split("_")[0] for p in positions],
            "µs",
            [by_id[f"legal_moves/{p}"]["median_ns"] / 1e3 for p in positions],
        ),
        "",
    ]
    return "\n".join(out)


def game_section(benches, game):
    step = ply_series(benches, game, "step")
    if not step:
        return ""
    comps = {c: ply_series(benches, game, c) for c in COMPONENTS}
    step_us = [b["median_ns"] / 1e3 for b in step]
    worst = max(step, key=lambda b: b["median_ns"])
    p95s = [b["p95_ns"] for b in step]
    total = sum(b["median_ns"] for b in step)
    legend = " · ".join(f"{SWATCH[i]} `{c}`" for i, c in enumerate(COMPONENTS) if comps[c])
    out = [
        f"### Per-ply cost: `{game}` game ({len(step)} plies)",
        "",
        "`step` = generate the legal moves, `Game::play` the move, then `Game::outcome` on the result: "
        "everything the engine does for one move.",
        "",
        "| | `step` | " + " | ".join(f"`{c}`" for c in COMPONENTS if comps[c]) + " |",
        "|---|--:|" + "--:|" * sum(1 for c in COMPONENTS if comps[c]),
    ]
    for label, fn in [
        ("median over plies", lambda rows: statistics.median(b["median_ns"] for b in rows)),
        ("slowest ply", lambda rows: max(b["median_ns"] for b in rows)),
        ("fastest ply", lambda rows: min(b["median_ns"] for b in rows)),
    ]:
        out.append(
            f"| {label} | {fmt_ns(fn(step))} | "
            + " | ".join(fmt_ns(fn(comps[c])) for c in COMPONENTS if comps[c])
            + " |"
        )
    out += [
        "",
        f"Whole game: **{fmt_ns(total)}** of engine time. Slowest ply: **{worst['ply']}** "
        f"(`{worst['move']}`, {worst['moves']} legal moves, {fmt_ns(worst['median_ns'])}). "
        f"Worst per-ply p95: {fmt_ns(max(p95s))}.",
        "",
        xychart(f"{game}: step time per ply (µs)", "ply", "µs", [step_us]),
        "",
        f"Breakdown: {legend}",
        "",
        xychart(
            f"{game}: components per ply (µs)",
            "ply",
            "µs",
            [[b["median_ns"] / 1e3 for b in comps[c]] for c in COMPONENTS if comps[c]],
        ),
        "",
    ]
    return "\n".join(out)


RESAMPLES = 1000


def resample(runs, rng):
    """One hierarchical bootstrap draw: pick runs with replacement, then samples within each."""
    pooled = []
    for run in rng.choices(runs, k=len(runs)):
        pooled += rng.choices(run, k=len(run))
    return statistics.median(pooled)


def percentile_ci(draws):
    draws.sort()
    return draws[int(0.025 * len(draws))], draws[int(0.975 * len(draws)) - 1]


def merge(runs_of_benches, rng):
    """Combine the same benchmark from several runs: pooled median and p95, hierarchical CI."""
    first = runs_of_benches[0]
    if len(runs_of_benches) == 1:
        return dict(first, runs=[first["samples_ns"]])
    runs = [b["samples_ns"] for b in runs_of_benches]
    pooled = sorted(x for r in runs for x in r)
    per_iter = [x for r in runs for x in r]
    return dict(
        first,
        runs=runs,
        samples_ns=per_iter,
        median_ns=statistics.median(pooled),
        p95_ns=pooled[int(0.95 * (len(pooled) - 1))],
        ci95_ns=list(percentile_ci([resample(runs, rng) for _ in range(RESAMPLES)])),
    )


def load_all(paths, rng):
    datas = [load(p) for p in paths]
    ids = [b["id"] for b in datas[0]["benchmarks"]]
    by_run = [{b["id"]: b for b in d["benchmarks"]} for d in datas]
    benches = [merge([r[i] for r in by_run if i in r], rng) for i in ids]
    commits = {d["environment"]["git_commit"] for d in datas}
    if len(commits) > 1:
        sys.exit(f"{paths}: runs come from different commits {commits}")
    env = dict(datas[0]["environment"], runs=len(datas))
    return {"environment": env, "benchmarks": benches}


def ratio_ci(new, old, rng):
    """Hierarchical-bootstrap 95% CI of median(new) / median(old)."""
    return percentile_ci([resample(new["runs"], rng) / resample(old["runs"], rng) for _ in range(RESAMPLES)])


def geomean(xs):
    return statistics.geometric_mean(xs)


def comparison_section(cur, base, threshold, label, rng):
    base_by_id = {b["id"]: b for b in base["benchmarks"]}
    rows, verdicts = [], {"faster": 0, "slower": 0, "same": 0}
    for b in cur["benchmarks"]:
        old = base_by_id.get(b["id"])
        if old is None:
            continue
        r = b["median_ns"] / old["median_ns"]
        lo, hi = ratio_ci(b, old, rng)
        if hi < 1 - threshold / 100:
            v = "faster"
        elif lo > 1 + threshold / 100:
            v = "slower"
        else:
            v = "same"
        verdicts[v] += 1
        rows.append((b, old, r, lo, hi, v))
    if not rows:
        return "No benchmarks in common with the baseline.\n"

    icon = {"faster": "🟢 faster", "slower": "🔴 slower", "same": "⚪ no change"}
    out = [
        f"### Comparison with {label}",
        "",
        f"**{verdicts['slower']}** slower · **{verdicts['faster']}** faster · **{verdicts['same']}** unchanged "
        f"out of {len(rows)} benchmarks (flagged when the 95% CI of the change excludes ±{threshold:g}%).",
        "",
        "| Benchmark | Baseline | Current | Change | 95% CI | |",
        "|---|--:|--:|--:|--:|---|",
    ]
    for b, old, r, lo, hi, v in rows:
        if b["id"].startswith("ply/"):
            continue
        out.append(
            f"| `{b['id']}` | {fmt_ns(per_unit(old))} | {fmt_ns(per_unit(b))} | {100 * (r - 1):+.1f}% "
            f"| [{100 * (lo - 1):+.1f}%, {100 * (hi - 1):+.1f}%] | {icon[v]} |"
        )
    for game in games(cur["benchmarks"]):
        for comp in ["step"] + COMPONENTS:
            sel = [x for x in rows if x[0]["id"].startswith(f"ply/{game}/{comp}/")]
            if not sel:
                continue
            flagged = [x[5] for x in sel if x[5] != "same"]
            out.append(
                f"| `ply/{game}/{comp}/*` ({len(sel)} plies, geomean) | "
                f"{fmt_ns(geomean([x[1]['median_ns'] for x in sel]))} | {fmt_ns(geomean([x[0]['median_ns'] for x in sel]))} "
                f"| {100 * (geomean([x[2] for x in sel]) - 1):+.1f}% | – | "
                f"{flagged.count('slower')} 🔴 / {flagged.count('faster')} 🟢 |"
            )
    out.append("")
    return "\n".join(out)


def methodology(env):
    return f"""<details><summary>Methodology</summary>

* **Batched samples.** Each sample times a batch of iterations sized (by doubling) to take at least
  {env['sample_target_ms']} ms, so clock overhead ({env['timer_overhead_ns']} ns) and resolution
  ({env['timer_resolution_ns']} ns) are well under 0.1% of a sample. Per-iteration time = batch time / iterations.
* **Warm-up.** {env['warmup_ms']} ms of CPU burn before measuring (frequency scaling, turbo), and the doubling
  calibration of every benchmark warms caches and branch predictors.
* **Interleaved rounds.** {env['samples']} rounds; each round takes one sample of *every* benchmark in a freshly
  shuffled order, so slow drift (thermal throttling, noisy neighbours) is spread across all benchmarks rather than
  biasing whichever ran during a bad stretch.
* **No dead-code elimination.** Inputs and outputs go through `std::hint::black_box` on every iteration.
* **Deterministic workloads.** Fixed FENs (move counts asserted against perft references), a fixed historical game,
  and a seeded random game (seed {env['seed']}), so runs are comparable.
* **Several processes.** {env['runs']} separate `cargo bench` invocation(s) per side. Heap placement and code
  layout differ between processes and can shift a benchmark by several percent, which samples within one
  process cannot reveal.
* **Robust statistics.** Median with a 95% hierarchical-bootstrap CI (resample runs, then samples within each
  run); outliers counted with Tukey's fences but kept. Comparisons use a bootstrap CI of the ratio of medians
  and a minimum effect size.
* **Build.** `cargo bench` profile: release optimizations, `codegen-units = 1` (stable code layout), no debug assertions.
</details>"""


def environment_table(env):
    keys = ["git_commit", "git_branch", "git_dirty", "rustc", "cpu", "logical_cpus", "governor", "kernel", "loadavg"]
    rows = "\n".join(f"| `{k}` | {env.get(k, '')} |" for k in keys)
    when = datetime.fromtimestamp(int(env["timestamp_unix"]), timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    return f"""<details><summary>Environment</summary>

| | |
|---|---|
{rows}
| `run at` | {when} |
</details>"""


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("current", nargs="+", help="JSON output of one or more runs of the same commit")
    ap.add_argument("--baseline", nargs="+", help="JSON from earlier runs to compare against")
    ap.add_argument("--baseline-label", default="baseline")
    ap.add_argument("--threshold", type=float, default=3.0, help="minimum change to flag, in percent")
    ap.add_argument("--title", default="Per-move benchmark")
    args = ap.parse_args()

    rng = random.Random(0)
    cur = load_all(args.current, rng)
    env, benches = cur["environment"], cur["benchmarks"]
    parts = [
        f"## {args.title}",
        "",
        f"`{env['git_commit'][:10]}` · {env['cpu']} ({env['logical_cpus']} CPUs) · {env['rustc']} · "
        f"{env['runs']} run(s) × {env['samples']} samples × {len(benches)} benchmarks",
        "",
    ]
    if env.get("debug_assertions"):
        parts.append("> [!WARNING]\n> Built with debug assertions: these numbers are not representative.\n")
    if args.baseline:
        base = load_all(args.baseline, rng)
        parts.append(comparison_section(cur, base, args.threshold, args.baseline_label, rng))
    parts.append(corpus_section(benches))
    for g in games(benches):
        parts.append(game_section(benches, g))
    parts += [methodology(env), "", environment_table(env), ""]
    print("\n".join(parts))


if __name__ == "__main__":
    main()
