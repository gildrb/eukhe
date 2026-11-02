from collections import Counter


def users_per_plan(users):
    return dict(Counter(u.plan for u in users))
