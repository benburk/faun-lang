#!/usr/bin/env python3
"""Write a JSON array of `count` user records to standard output: integers,
floats with two decimals, strings with escapes and non-ASCII text, booleans,
null, nested objects and arrays. The same count always writes the same text.

    python3 generate.py 20000 > users.json"""

import json
import random
import sys

CITIES = ["Zürich", "Montréal", "Kyōto", "São Paulo", "Oslo", "Lagos"]
WORDS = ["alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta"]


def user(rng, index):
    return {
        "id": index,
        "name": f"user{index}",
        "email": f"user{index}@example.com",
        "active": rng.random() < 0.5,
        # Never whole, so every language writes it back with its decimals.
        "score": round(rng.randint(0, 999) + rng.randint(1, 99) / 100, 2),
        "tags": rng.sample(WORDS, rng.randint(0, 4)),
        "address": {"city": rng.choice(CITIES), "zip": f"{rng.randint(0, 99999):05d}"},
        "friends": [rng.randint(0, 10**12) for _ in range(rng.randint(0, 5))],
        "note": None if rng.random() < 0.7 else f'said "hi"\tat {index}\n',
    }


def main():
    count = int(sys.argv[1])
    rng = random.Random(count)
    users = [user(rng, index) for index in range(count)]
    json.dump(users, sys.stdout, ensure_ascii=False, separators=(",", ":"))


if __name__ == "__main__":
    main()
