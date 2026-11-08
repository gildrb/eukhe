"""Read ledger CSV lines: date,category,amount,currency."""
from dataclasses import dataclass


@dataclass(frozen=True)
class Entry:
    date: str
    category: str
    amount_cents: int
    currency: str


def parse_amount(text):
    """'3.50' -> 350 (cents)."""
    return int(float(text) * 100)


def parse_line(line):
    date, category, amount, currency = [p.strip() for p in line.split(",")]
    return Entry(date, category, parse_amount(amount), currency.upper())


def parse_file(path):
    entries = []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            entries.append(parse_line(line))
    return entries
