# facts, vendored

A small C/C++ testing library by the owner: `FACT(a == b)` prints both values when it fails, and
`FACTS_TRACE` says which case of a loop it was. Used by the course (`course/`): the tests it starts
from, before the proofs. (Copied from gosh's `vendor/facts`, 2026-11-21.) MIT (`LICENSE`), which GPL-3.0-or-later code may use.

- **From:** github.com/wmacevoy/facts, tag `v2.4.1`, commit `2f3cb3c3b10c30b7728aad45f56d3bc5d7d815e5`.
- **What:** `include/facts.h`, `src/facts.c`, `src/facts.cpp`, `LICENSE`, copied unchanged. To
  update: copy the same four from a newer tag, and change the two lines above.
- **How it is built:** `tools/build.sh` copies this directory into its copy of the core, at
  `vendor/facts/`. A part's tests include `"vendor/facts/facts.h"` and link `libfacts.a`, built in
  that part's directory from `facts.cpp` (which includes `facts.c`) without gosh's warning flags,
  as code that is not gosh's.

Taken on 2026-11-17 on the owner's word ("yes to both, start with facts"), tried on
`src/meetup/registrations-test.cc`; then every unit test was moved to it ("fix all the tests"):
how they are written is in `CONTRIBUTING.md`.
