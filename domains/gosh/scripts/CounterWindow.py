#!/usr/bin/env python3
"""Calls for CounterWindow that the seeded counters would almost never make: counters near each
other, either side of the window's 1024, used twice, and at the two ends of 64 bits. Seeded: the
same every run. (One object takes every call, so the walk moves on from wherever it is.)"""
import random

rng = random.Random(20261118)
M = (1 << 64) - 1
base = rng.randrange(1 << 62)
for k in range(6000):
    if k == 4000:
        base = M - 2000          # up to the top of 64 bits, and round it
    r = rng.randrange(7)
    if r == 0:
        c = base + rng.randrange(2200) - 1100
    elif r == 1:
        c = base + rng.randrange(5)
    elif r == 2:
        c = base - rng.randrange(1030)
    elif r == 3:
        c = base + 1000 + rng.randrange(60)
    else:
        c = base + rng.randrange(130) - 65
    c &= M
    print("0 %d" % c)
    if rng.random() < 0.3:
        base = c
