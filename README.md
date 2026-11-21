# strong-domain-driven-design

*Private. Started 2026-11-18.*

"the goal is to learn from proving the boundaries of gosh, which might change its shape."
*(the owner, 2026-11-18; `docs/REQUIREMENTS_v2.md`, a draft)*

This project is the approach: how to write code so that it is easy to reason about and prove,
and the prover that holds it. gosh is the program it learns from.

A domain is a C++ class whose state is all `private`. For each domain, a proof checked by
[Lean 4](https://lean-lang.org) shows that no method commits a memory error, every loop ends,
and the class's own `invariant()`, if it has one, is always true. What must be proven is derived
from the program's own text by the generator in `prover/`; the proofs are hints: anyone may write
them, and an audit checks them without trusting them.

gosh's proofs stand in gosh, beside the classes they prove, and gosh's own check runs them
(since 2026-11-21; until then they were here, in `domains/gosh`). This project owns the prover and
its tools (Lean, by `tools/lean.sh`; a Python with libclang, by `pixi install`), and its check runs
gosh's proofs by this prover.

```sh
tools/lean.sh && pixi install      # once: Lean 4.36.0 into .tools/, and the Python with libclang into .pixi/
tools/check.sh                     # the prover's own tests, then gosh's proofs by it (../gosh, built); success prints "check: PASS"
```

## The map: gosh's boundaries

The whole map is `docs/MAP.md`: 29 places where bytes or calls come in to gosh, from reading gosh
at `d0cfd4f` (read, not run). In short:

| From | Places | Proved | Assumed | Not yet |
| ---- | ------ | ------ | ------- | ------- |
| anyone on the Internet, before any key | 6 | 1 (the STUN answer read: `StunAnswer`, on gosh's branch `strong/main`, not on main), and part of 1 (the meetup's `is_stun_request`, as it is on main) | 1 (a session datagram: mosh's core) | 3, and the rest of that 1 |
| whoever holds a key: the other end, a ticket's holder | 9 | part of 1 (the meetup's `CounterWindow` and the `bounded` number it takes, on gosh's branch `strong/main`: memory, ending, and that the highest counter kept is at most 2^62 - 1; not that no counter is taken twice. And what a meetup message is sealed with, `MeetupNonce`: no two of a key's four senders make one nonce; not that a sender's counter is never used twice. What is not proved hands it a number that is tested when the program runs, and the process ends if the test fails) | 1 (the fields gosh adds to mosh's instruction, read by protobuf) | 7, and the rest of that 1 |
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
| `course/` | a course: from facts to proofs, for a junior student, ending at proving a merge sort correct (`course/README.md`) |
| `docs/STRONG_DOMAINS.md` | the approach: the shape of strong domains, held by design, test and proof; how the prover grows; guidelines (a draft) |
| `docs/ALTERNATIVES.md` | ten other ways to hold a design by proof, what each would mean for gosh, and what to take from each (a draft; recalled and searched, nothing run) |
| `prover/` | the generator, the lint and the audit: `prover/README.md` |
| `tools/check.sh` | the check |
| `tools/lean.sh`, `pixi.toml` | the prover's tools: Lean, and a Python with libclang |
| `tools/image/` | the same tools as an image, for a program's CI (`.github/workflows/image.yml` publishes it) |
| `vendor/se1/` | the software-engineering guide this project follows, v1.7 |
| `CONTRIBUTING.md` | how to run it |
