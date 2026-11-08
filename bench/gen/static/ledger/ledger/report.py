"""Totals and formatting."""
from .convert import to_eur_cents


def totals_by_category(entries):
    totals = {}
    for e in entries:
        totals[e.category] = totals.get(e.category, 0) + to_eur_cents(e.amount_cents, e.currency)
    return totals


def format_total(cents):
    """1205 -> '€12.05'."""
    return f"€{cents // 100}.{cents % 100}"


def summary_lines(entries):
    totals = totals_by_category(entries)
    return [f"{cat}: {format_total(totals[cat])}" for cat in sorted(totals)]
