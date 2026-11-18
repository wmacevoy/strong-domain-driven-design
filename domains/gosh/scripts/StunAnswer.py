#!/usr/bin/env python3
"""Calls for StunAnswer that the seeded bytes would almost never make: answers with a right header,
and attributes right, wrong, cut short, and lying about their lengths. Seeded: the same every run."""
import random

rng = random.Random(20261117)
COOKIE = bytes([0x21, 0x12, 0xA4, 0x42])


def attribute(txid):
    kind = rng.choice([0x0020, 0x0020, 0x0001, 0x0001, 0x8022, rng.randrange(65536)])
    family = rng.choice([1, 1, 2, 2, rng.randrange(256)])
    port = bytes(rng.randrange(256) for _ in range(2))
    if family == 2:
        address = rng.choice([
            bytes(rng.randrange(256) for _ in range(16)),
            bytes(a ^ b for a, b in zip(bytes([0xfe, 0x80 | rng.randrange(64)]) + bytes(rng.randrange(256) for _ in range(14)), COOKIE + txid)),
            bytes(a ^ b for a, b in zip(bytes(10) + b"\xff\xff" + bytes(rng.randrange(256) for _ in range(4)), COOKIE + txid)),
            bytes(a ^ b for a, b in zip(bytes(9) + bytes([rng.randrange(2)]) + b"\xff\xff" + bytes(4), COOKIE + txid)),
        ])
    else:
        address = bytes(rng.randrange(256) for _ in range(rng.choice([4, 4, 4, 16, 2])))
    value = bytes([rng.randrange(256), family]) + port + address
    if rng.random() < 0.15:
        value = value[:rng.randrange(len(value) + 1)]
    size = len(value) if rng.random() < 0.85 else rng.randrange(65536)
    return bytes([kind >> 8, kind & 255, size >> 8, size & 255]) + value + bytes(-len(value) % 4)


def answer():
    txid = bytes(rng.randrange(256) for _ in range(12))
    body = b"".join(attribute(txid) for _ in range(rng.randrange(4)))
    said = len(body) if rng.random() < 0.8 else rng.randrange(65536)
    whole = bytes([0x01, 0x01, said >> 8, said & 255]) + COOKIE + txid + body
    r = rng.random()
    if r < 0.1:
        whole = whole[:rng.randrange(len(whole) + 1)]
    elif r < 0.2:
        i = rng.randrange(len(whole))
        whole = whole[:i] + bytes([rng.randrange(256)]) + whole[i + 1:]
    return whole


for _ in range(1500):
    print("0 %s" % (answer().hex() or "-"))
    print("1")
    print("2")
    for i in rng.sample(range(18), 6):
        print("3 %d" % i)
