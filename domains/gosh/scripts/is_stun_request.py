#!/usr/bin/env python3
"""Calls for is_stun_request that seeded bytes would almost never make: requests with a right
header, of every length either side of 20 and 200, and with one byte of the header wrong.
Seeded: the same every run."""
import random

rng = random.Random(20261118)
HEAD = bytes([0x00, 0x01, 0x00, 0x00, 0x21, 0x12, 0xA4, 0x42])
for _ in range(3000):
    n = rng.choice([0, 1, 7, 8, 19, 20, 21, 199, 200, 201, rng.randrange(260)])
    whole = (HEAD + bytes(rng.randrange(256) for _ in range(260)))[:n]
    if whole and rng.random() < 0.3:
        i = rng.randrange(min(len(whole), 8))
        whole = whole[:i] + bytes([rng.randrange(256)]) + whole[i + 1:]
    print("0 %s" % (whole.hex() or "-"))
