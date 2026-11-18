#!/usr/bin/env python3
"""
REQ1/RED-1: for each proved domain, the model broken in the ways its proof is there to prevent,
and each proof seen to fail. A case is a copy of domains/gosh with one edit, then oopc's prove.sh.

Usage: LEAN=/path/to/lean python3 tools/red-test.py     (seen red 2026-11-18; about a minute)
"""
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOMAIN = os.path.join(ROOT, "domains", "gosh")
PROVE = os.path.join(ROOT, "oopc", "cpp-proof-gen", "prove.sh")

# (the class, its file's text as it is, the text broken, what is owed that no longer holds)
CASES = [
    ("StunAnswer", "      if (at + 4 + size > 20 + body) break;\n", "",
     "an attribute's length is not tested against the body: a read outside the bytes"),
    ("StunAnswer", "type == 0x0020 && size >= 20 &&", "type == 0x0020 && size >= 4 &&",
     "an IPv6 value of 4 bytes is taken for 20: a read outside the bytes"),
    ("StunAnswer", "for (uint64_t k = 0; k < 16; k = k + 1)", "for (uint64_t k = 0; k < 17; k = k + 1)",
     "17 bytes are copied into 16: a write outside the address"),
    ("StunAnswer", "at = at + 4 + ((size + 3) & ~(uint64_t)3);", "at = at + ((size + 3) & ~(uint64_t)3);",
     "the loop does not move on: an attribute of no length would hold it for ever"),
    ("StunAnswer", "!(b0 == 0xfe && (b1 & 0xc0) == 0x80)", "!(b0 == 0xfd && (b1 & 0xc0) == 0x80)",
     "fd80 is tested where fe80 is meant: an address of one link alone is kept (the invariant)"),
    ("CounterWindow", "seen[(i & 1023) >> 6] = seen[(i & 1023) >> 6] & ~(one << (i & 63));",
     "seen[(i & 2047) >> 6] = seen[(i & 1023) >> 6] & ~(one << (i & 63));",
     "a counter's low eleven bits choose the word: a write outside the sixteen"),
    ("CounterWindow", ">> (c & 63)) & 1) != 0", ">> (c & 127)) & 1) != 0",
     "a shift by up to 127 of 64 bits: undefined"),
    ("CounterWindow", "i <= c && i - top <= 1024; i = i + 1", "i <= c; i = i + 1",
     "the loop is not held to 1024 rounds: a counter of 2^64-1 would hold the meetup for ever"),
    ("CounterWindow", "      any = 1;\n", "      any = 2;\n",
     "the flag is given a value that is not 0 or 1 (the invariant)"),
]

failures = 0
for klass, old, new, what in CASES:
    with tempfile.TemporaryDirectory() as d:
        work = os.path.join(d, "domain")
        shutil.copytree(DOMAIN, work, ignore=shutil.ignore_patterns("build", "gen"))
        path = os.path.join(work, "model", klass + ".hpp")
        text = open(path).read()
        assert text.count(old) == 1, (klass, old)
        open(path, "w").write(text.replace(old, new))
        r = subprocess.run(["sh", PROVE, klass], capture_output=True, text=True, env=dict(os.environ, DOMAIN=work))
        out = r.stdout + r.stderr
        ok = r.returncode == 1 and "a proof does not hold" in out
        print("red: %s: %s: %s" % (klass, what, "the proof fails, ok" if ok else "FAIL (exit %d) %s" % (r.returncode, out.strip()[-200:])))
        failures += not ok
print("red: FAIL: %d" % failures if failures else "red: PASS (%d cases)" % len(CASES))
sys.exit(1 if failures else 0)
