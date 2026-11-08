import unittest
from datetime import date

from crm.stats import users_per_plan
from crm.users import User


class StatsTests(unittest.TestCase):
    def test_users_per_plan(self):
        users = [User(1, "a", True, date(2026, 1, 1), "pro"), User(2, "b", True, date(2026, 1, 1), "pro")]
        self.assertEqual(users_per_plan(users), {"pro": 2})


if __name__ == "__main__":
    unittest.main()
