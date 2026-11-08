"""Currency conversion to EUR."""

# How many EUR one unit of the currency is worth.
RATES = {"EUR": 1.0, "USD": 0.9, "GBP": 1.2}


def to_eur_cents(amount_cents, currency):
    rate = RATES[currency]
    return round(amount_cents / rate)
