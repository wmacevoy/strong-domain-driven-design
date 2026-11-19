# strong-domain-driven-design

*Private. Started 2026-11-18.*

"the goal is to learn from proving the boundaries of gosh, which might change its shape."
*(the owner, 2026-11-18; `docs/REQUIREMENTS_v1.md`, a draft)*

A domain is a C++ class whose state is all `private`. For each domain taken from gosh, this
project holds a proof, checked by [Lean 4](https://lean-lang.org), that no method commits a memory
error, every loop ends, and the class's own `invariant()`, if it has one, is always true. What must
be proven is derived from gosh's own text, read as committed on a named branch of `../gosh` at every
check, by the generator in `prover/`. No copy of gosh's code is written by hand. Where
gosh's text cannot be read as it is, gosh is reshaped on a branch named `strong/...`, which passes
gosh's own check first. The proofs
are hints: anyone may write them, and an audit checks them without trusting them.

```sh
PYTHON=/path/to/python-with-libclang tools/check.sh      # reads ../gosh at the branch strong/main (GOSH, GOSH_REF); about a minute; success prints "check: PASS"
```

## The map: gosh's boundaries

The whole map is `docs/MAP.md`: 29 places where bytes or calls come in to gosh, from reading gosh
at `d0cfd4f` (read, not run). In short:

| From | Places | Proved | Assumed | Not yet |
| ---- | ------ | ------ | ------- | ------- |
| anyone on the Internet, before any key | 6 | 1 (the STUN answer read: `StunAnswer`, on gosh's branch `strong/main`, not on main), and part of 1 (the meetup's `is_stun_request`, as it is on main) | 1 (a session datagram: mosh's core) | 3, and the rest of that 1 |
| whoever holds a key: the other end, a ticket's holder | 9 | part of 1 (the meetup's `CounterWindow` and the `bounded` number it takes, on gosh's branch `strong/main`: memory, ending, and that the highest counter kept is at most 2^62 - 1; not that no counter is taken twice. What is not proved hands it a number that is tested when the program runs, and the process ends if the test fails) | 1 (the fields gosh adds to mosh's instruction, read by protobuf) | 7, and the rest of that 1 |
| the host, through ssh | 5 | 0 | 0 | 5 |
| this machine | 9 | 0 | 0 | 9 |

ssh, mosh's core, the cipher and the kernel are assumed, by the owner's decision.

## What "proved" rests on

The compiler and the machine are correct, and the domain is called correctly (the owner's
assumptions). Also: everything else in the program commits no memory error; the generator reads the
C++ rightly (tested by comparison, not proved); the invariant says enough (it is a few lines of the
C++, for a person to read); Lean's kernel, library and three standard axioms.

## Where things are

| | |
|---|---|
| `docs/` | requirements (a draft), design, queue, findings |
| `domains/gosh/` | which classes and functions of gosh are read (`from/`), the proofs (`claims/`), inputs for the comparison (`scripts/`), and what was generated (`gen/`) |
| `prover/` | the generator, the lint and the audit: `prover/README.md` |
| `tools/check.sh` | the check |
| `vendor/se1/` | the software-engineering guide this project follows, v1.7 |
| `CONTRIBUTING.md` | how to run it |
