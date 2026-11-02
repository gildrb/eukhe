#!/usr/bin/env python3
"""Run many run.py jobs in parallel, tools interleaved; skips runs that have a summary (unless --rerun).

batch.py [flags] --tools eukhe,omp --tasks crm,relay|all --runs 1,2,3 [--par 4]. Logs: <dir>/logs/.
"""
import argparse
import concurrent.futures
import subprocess
import sys

import run as runmod
import settings
import tasks


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tools", default="eukhe", help="comma list of eukhe, omp")
    ap.add_argument("--tasks", default="all", help=f"comma list or `all`: {', '.join(tasks.TASKS)}")
    ap.add_argument("--runs", default="1", help="comma list of run numbers")
    ap.add_argument("--par", type=int, default=4, help="runs at once")
    ap.add_argument("--tag", help="label suffix (see run.py)")
    ap.add_argument("--rerun", action="store_true", help="run again even when a summary exists")
    settings.add_flags(ap)
    args = ap.parse_args()
    settings.apply(args)
    tools = args.tools.split(",")
    names = list(tasks.TASKS) if args.tasks == "all" else args.tasks.split(",")
    for t in names:
        if t not in tasks.TASKS:
            raise SystemExit(f"bench: unknown task {t}")
    for t in tools:
        if t not in ("eukhe", "omp"):
            raise SystemExit(f"bench: unknown tool {t}")
    model = settings.get("model") or None
    runmod.prepare(set(tools))
    data = settings.path("dir")
    jobs = [(tool, task, run) for run in args.runs.split(",") for task in names for tool in tools
            if args.rerun or not (data / "results" / runmod.label_of(tool, model, args.tag) / task / run /
                                  "summary.json").exists()]
    (data / "logs").mkdir(parents=True, exist_ok=True)

    def one(job):
        tool, task, run = job
        log = data / "logs" / f"{runmod.label_of(tool, model, args.tag)}-{task}-{run}.log"
        cmd = [sys.executable, "-B", str(settings.BENCH / "run.py"), tool, task, run]
        if args.tag:
            cmd += ["--tag", args.tag]
        with open(log, "w") as fh:
            rc = subprocess.run(cmd, stdout=fh, stderr=subprocess.STDOUT).returncode
        return job, rc, log.read_text().strip().splitlines()[-1:]

    failed = 0
    with concurrent.futures.ThreadPoolExecutor(args.par) as ex:
        for job, rc, lines in ex.map(one, jobs):
            failed += rc != 0
            print(*job, f"exit={rc}", *lines, sep="  ", flush=True)
    print(f"batch done: {len(jobs)} runs, {failed} harness failures", flush=True)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
