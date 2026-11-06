"""The decode benchmark in Python: users read into classes, and written back."""

from dataclasses import dataclass
import json
import sys


@dataclass
class Address:
    city: str
    zip: str


@dataclass
class User:
    id: int
    name: str
    email: str
    active: bool
    score: float
    tags: list
    address: Address
    friends: list
    note: str | None


def user(record):
    address = record["address"]
    return User(
        record["id"],
        record["name"],
        record["email"],
        record["active"],
        record["score"],
        record["tags"],
        Address(address["city"], address["zip"]),
        record["friends"],
        record["note"],
    )


def written(user):
    return {
        "id": user.id,
        "name": user.name,
        "email": user.email,
        "active": user.active,
        "score": user.score,
        "tags": user.tags,
        "address": {"city": user.address.city, "zip": user.address.zip},
        "friends": user.friends,
        "note": user.note,
    }


users = [user(record) for record in json.loads(sys.stdin.buffer.read())]
text = json.dumps(
    [written(u) for u in users], ensure_ascii=False, separators=(",", ":")
)
active = sum(1 for u in users if u.active)
tags = sum(len(u.tags) for u in users)
print(f"users {len(users)} active {active} tags {tags} bytes {len(text.encode())}")
