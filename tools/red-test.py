#!/usr/bin/env python3
"""
REQ1/RED-1: for each proved domain, its text broken in the ways its proof is there to prevent,
and each proof seen to fail. A case is a copy of domains/gosh with one edit, then oopc's prove.sh.
A class read from gosh itself (domains/gosh/from/C) is broken in a copy of gosh's file: gosh is
never written to. If gosh's text no longer has the line a case breaks, the case fails, and says so.

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
    ("StunAnswer", "      if ( at + 4 + size > 20 + body ) {\n        break;\n      }\n", "",
     "an attribute's length is not tested against the body: a read outside the bytes"),
    ("StunAnswer", "type == 0x0020 && size >= 20 &&", "type == 0x0020 && size >= 4 &&",
     "an IPv6 value of 4 bytes is taken for 20: a read outside the bytes"),
    ("StunAnswer", "for ( uint64_t k = 0; k < 16; k++ )", "for ( uint64_t k = 0; k < 17; k++ )",
     "17 bytes are copied into 16: a write outside the address"),
    ("StunAnswer", "at = at + 4 + ( ( size + 3 ) & ~static_cast<uint64_t>( 3 ) );", "at = at + ( ( size + 3 ) & ~static_cast<uint64_t>( 3 ) );",
     "the loop does not move on: an attribute of no length would hold it for ever"),
    ("StunAnswer", "!( b0 == 0xfe && ( b1 & 0xc0 ) == 0x80 )", "!( b0 == 0xfd && ( b1 & 0xc0 ) == 0x80 )",
     "fd80 is tested where fe80 is meant: an address of one link alone is kept (the invariant)"),
    ("CounterWindow", "void clear( uint64_t c ) { seen[( c % WINDOW ) / 64] &=", "void clear( uint64_t c ) { seen[( c % WINDOW ) / 32] &=",
     "a word is chosen among 32 where there are 16: a write outside them"),
    ("CounterWindow", ">> ( c % 64 ) ) & 1;", ">> ( c % 128 ) ) & 1;",
     "a shift by up to 127 of 64 bits: undefined"),
    ("CounterWindow", "i <= c && i - top <= WINDOW; i++", "i <= c; i++",
     "the loop is not held to 1024 rounds: a counter of 2^64-1 would hold the meetup for ever"),
    ("CounterWindow", "static const uint64_t WINDOW = 1024;", "static const uint64_t WINDOW = 1025;",
     "a window of 1025 (the array is still 16 words): a remainder of 1024 chooses a seventeenth"),
    ("is_stun_request", "n < 20 ||", "n < 7 ||",
     "seven bytes are taken for enough: the eighth is read outside them"),
]

failures = 0
for klass, old, new, what in CASES:
    with tempfile.TemporaryDirectory() as d:
        work = os.path.join(d, "domain")
        shutil.copytree(DOMAIN, work, ignore=shutil.ignore_patterns("build", "gen"))
        env = dict(os.environ, DOMAIN=work)
        path = os.path.join(work, "model", klass + ".hpp")
        if os.path.exists(os.path.join(work, "from", klass)):       # gosh's own file: a copy of it, alone
            rel = open(os.path.join(work, "from", klass)).read().split()[0]       # (a second word says "function")
            path = os.path.join(d, "subject", rel)
            os.makedirs(os.path.dirname(path))
            shutil.copy(os.path.join(os.environ["SUBJECT"], rel), path)
            env["SUBJECT"] = os.path.join(d, "subject")
        text = open(path).read()
        if text.count(old) != 1:
            print("red: %s: FAIL: the text this case breaks is there %d times, not once: %r" % (klass, text.count(old), old))
            failures += 1
            continue
        open(path, "w").write(text.replace(old, new))
        r = subprocess.run(["sh", PROVE, klass], capture_output=True, text=True, env=env)
        out = r.stdout + r.stderr
        ok = r.returncode == 1 and "a proof does not hold" in out
        print("red: %s: %s: %s" % (klass, what, "the proof fails, ok" if ok else "FAIL (exit %d) %s" % (r.returncode, out.strip()[-200:])))
        failures += not ok
print("red: FAIL: %d" % failures if failures else "red: PASS (%d cases)" % len(CASES))
sys.exit(1 if failures else 0)
