import argparse
from datetime import date

from .stats import users_per_plan
from .users import load_users


def main():
    ap = argparse.ArgumentParser(prog="python -m crm")
    sub = ap.add_subparsers(dest="cmd", required=True)
    rp = sub.add_parser("report")
    rp.add_argument("file")
    rp.add_argument("--today", type=date.fromisoformat, default=date.today())
    args = ap.parse_args()
    users = load_users(args.file)
    print(f"users: {len(users)}")
    for plan, n in sorted(users_per_plan(users).items()):
        print(f"plan {plan}: {n}")


if __name__ == "__main__":
    main()
