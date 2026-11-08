#!/usr/bin/env python3
"""Markdown table of <dir>/results/<label>/<task>/<run>/summary.json: report.py [flags] [--tasks a,b] [--labels a,b].

Cost and tool calls come from the session storages under each run's HOME (children included); wall time is the
sum of the turns' walls; pass counts runs whose every check held.
"""
import argparse
import collections
import json
import sys

import settings
import tasks


def mean(xs):
    return sum(xs) / len(xs) if xs else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tasks", help="comma list (default: every task with results, in suite order)")
    ap.add_argument("--labels", help="comma list of result labels (default: all)")
    settings.add_flags(ap)
    args = ap.parse_args()
    settings.apply(args)
    runs = collections.defaultdict(list)
    for p in sorted((settings.path("dir") / "results").glob("*/*/*/summary.json")):
        s = json.loads(p.read_text())
        runs[(s["task"], s["label"])].append(s)
    if not runs:
        sys.exit(f"bench: no results under {settings.path('dir') / 'results'}")
    labels = args.labels.split(",") if args.labels else sorted({label for _, label in runs})
    want = args.tasks.split(",") if args.tasks else [t for t in tasks.TASKS if any((t, lb) in runs for lb in labels)]
    total = 0.0
    print("| task | label | model | pass | checks | wall min | cost $ | tool calls | failed checks |")
    print("|---|---|---|---|---|---|---|---|---|")
    for task in want:
        for label in labels:
            rs = runs.get((task, label), [])
            if not rs:
                continue
            passed = sum(1 for r in rs if r["passed"])
            ok = sum(sum(r["checks"].values()) for r in rs)
            n = sum(len(r["checks"]) for r in rs)
            wall = mean([sum(t["wall_s"] for t in r["turns"]) / 60 for r in rs])
            cost = mean([r["storage"]["cost"] for r in rs])
            calls = mean([r["storage"]["tool_calls"] for r in rs])
            total += sum(r["storage"]["cost"] for r in rs)
            models = ",".join(sorted({r["model"][1] for r in rs}))
            failed = collections.Counter(k for r in rs for k, v in r["checks"].items() if not v)
            print(f"| {task} | {label} | {models} | {passed}/{len(rs)} | {ok}/{n} | {wall:.1f} | {cost:.2f} | "
                  f"{calls:.0f} | {', '.join(f'{k}×{c}' for k, c in failed.items())} |")
    print(f"\ntotal recorded cost: ${total:.2f}")


if __name__ == "__main__":
    main()
