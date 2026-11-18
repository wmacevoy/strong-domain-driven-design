# strong-domain-driven-design

*Private. Started 2026-11-18.*

"the goal is to learn from proving the boundaries of gosh, which might change its shape."
*(the owner, 2026-11-18; `docs/REQUIREMENTS_v1.md`, a draft)*

A domain is a C++ class whose state is all `private`. For each domain taken from gosh, this
project holds a model of it and a proof, checked by [Lean 4](https://lean-lang.org), that no method
commits a memory error, every loop ends, and the class's own `invariant()` is always true. What
must be proven is derived from the C++ alone, by the generator in `oopc/` (a submodule). The proofs
are hints: anyone may write them, and an audit checks them without trusting them.

```sh
PYTHON=/path/to/python-with-libclang tools/check.sh      # about a minute; success prints "check: PASS"
```

## The map: gosh's boundaries

| Boundary of gosh | State | Where |
| ---------------- | ----- | ----- |
| a STUN answer read (`src/pathfinding/stun.h`, `stun_parse`) | **a model is proved**: for every sequence of bytes, `parse` ends, reads and writes nothing out of bounds, keeps only nothing, IPv4 or IPv6, and never an IPv6 address of one link alone. That the model is gosh's code was tested on 2026-11-17, outside this repository, and is not shown here | `domains/gosh/model/StunAnswer.hpp` |
| every other boundary | not yet looked at: the list itself is not made (`docs/QUEUE.md`) | |
| ssh, mosh's core, the cipher, the kernel | assumed, by the owner's decision | |

## What "proved" rests on

The compiler and the machine are correct, and the domain is called correctly (the owner's
assumptions). Also: everything else in the program commits no memory error; the generator reads the
C++ rightly (tested by comparison, not proved); the invariant says enough (it is a few lines of the
C++, for a person to read); Lean's kernel, library and three standard axioms.

## Where things are

| | |
|---|---|
| `docs/` | requirements (a draft), design, queue, findings |
| `domains/gosh/` | models of gosh's domains, their proofs (`claims/`), inputs for the comparison (`scripts/`), and what was generated (`gen/`) |
| `oopc/` | the generator and the audit: `oopc/cpp-proof-gen/README.md` |
| `tools/check.sh` | the check |
| `vendor/se1/` | the software-engineering guide this project follows, v1.7 |
| `CONTRIBUTING.md` | how to run it |
