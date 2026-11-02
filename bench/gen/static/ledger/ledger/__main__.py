import sys

from .parse import parse_file
from .report import summary_lines


def main(argv):
    if len(argv) != 2 or argv[0] != "summary":
        print("usage: python -m ledger summary FILE", file=sys.stderr)
        return 2
    for line in summary_lines(parse_file(argv[1])):
        print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
