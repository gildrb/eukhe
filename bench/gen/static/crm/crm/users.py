import json
from dataclasses import dataclass
from datetime import date


@dataclass(frozen=True)
class User:
    id: int
    name: str
    active: bool          # account enabled (false = suspended)
    last_login: date
    plan: str             # free | trial | pro | team


def load_users(path):
    with open(path, encoding="utf-8") as fh:
        raw = json.load(fh)
    return [User(u["id"], u["name"], u["active"], date.fromisoformat(u["last_login"]), u["plan"])
            for u in raw]
