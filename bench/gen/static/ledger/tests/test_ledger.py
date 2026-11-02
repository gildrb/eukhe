import unittest

from ledger.convert import to_eur_cents
from ledger.parse import parse_amount, parse_line
from ledger.report import format_total, totals_by_category


class LedgerTests(unittest.TestCase):
    def test_parse_amount(self):
        self.assertEqual(parse_amount("3.50"), 350)
        self.assertEqual(parse_amount("0.29"), 29)

    def test_parse_line(self):
        e = parse_line("2026-03-01, coffee, 3.50, eur")
        self.assertEqual((e.category, e.amount_cents, e.currency), ("coffee", 350, "EUR"))

    def test_usd_to_eur(self):
        self.assertEqual(to_eur_cents(1000, "USD"), 900)

    def test_format_total(self):
        self.assertEqual(format_total(1205), "€12.05")
        self.assertEqual(format_total(70000), "€700.00")

    def test_totals(self):
        entries = [parse_line("2026-03-01,a,1.00,GBP"), parse_line("2026-03-01,a,1.00,EUR")]
        self.assertEqual(totals_by_category(entries), {"a": 220})


if __name__ == "__main__":
    unittest.main()
