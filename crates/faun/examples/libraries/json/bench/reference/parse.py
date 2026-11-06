"""The parse benchmark in Python: every value counted, integers summed, and
string bytes added, member names included."""

import json
import sys


def tally(value, sums):
    sums[0] += 1
    if isinstance(value, bool) or value is None or isinstance(value, float):
        return
    if isinstance(value, int):
        sums[1] += value
    elif isinstance(value, str):
        sums[2] += len(value.encode())
    elif isinstance(value, list):
        for element in value:
            tally(element, sums)
    else:
        for name, member in value.items():
            sums[2] += len(name.encode())
            tally(member, sums)


sums = [0, 0, 0]
tally(json.loads(sys.stdin.buffer.read()), sums)
print(f"values {sums[0]} ints {sums[1]} strings {sums[2]}")
