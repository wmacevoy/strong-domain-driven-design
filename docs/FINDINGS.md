# Findings

What we learned the expensive way: surprises, dead ends, measurements, the attack that worked. The
only document reality writes
([SE1/W10](https://github.com/wmacevoy/software-engineering/blob/v1.7/guide/08-work.md#w10)).
Blameless: say what would have found it, not who should have asked. What was learned about the
generator itself is in `oopc/docs/FINDINGS.md`; here is what bears on gosh and on the method.

## 2026-11-18 — the first boundary of gosh proved as a model, and what it took

- **What happened:** gosh's `stun_parse` was written again as a class in the generator's subset
  (144 lines) and proved, for every sequence of bytes of any length: it ends, it reads and writes
  nothing out of bounds, it keeps only nothing, IPv4 or IPv6, and never an IPv6 address of one link
  alone (gosh's REQ17/PATH-8). The claims are 388 lines, checked in 9 seconds. Five ways of breaking
  the parser each make the proof fail (`tools/red-test.py`). Before this project existed (2026-11-17),
  gosh's real function, the model and the Lean model gave the same answers on 15,500 seeded calls
  and on gosh's own fuzz corpus; that comparison is not in this repository yet (queue 2).
- **What it suggests about gosh's shape** *(the agent's reading; the owner judges)*:
  - gosh's function takes `const char*`, a length, and a result by reference. The model takes a
    byte view (a pointer and a length in one value, read only through `at()` and `size()`) and
    keeps its result as its own private state. A boundary that takes bytes from outside may want
    that shape in gosh itself.
  - The model had to say an invariant, and gosh's function has none written: "never an address of
    one link alone" was in a comment and a requirement. Writing it as code is what made it provable.
  - The model uses only unsigned arithmetic, because signed overflow has no meaning to prove.
  - Not proved, and so still only tested: that IPv4 in IPv6's form is kept as IPv4, and anything
    about the port. The invariant does not say them.
- **Kind:** K2 (surprises), three of them, in oopc's findings: a loop needs a stated bound; one
  large function could not be reasoned about until the generator cut it into branches; and the
  claims name intermediate values by the expressions Lean shows, so a change to the C++ may make
  much of them untrue (not yet measured: queue 5).
- **Cost:** two sessions for the generator's loops, byte view, invariant and audit, and this proof.
- **Findable by:** trying a real parser rather than the two toy classes of the first spike.
- **Changed:** this project exists; the map in the README has its first row; queue items 2 to 7.

## 2026-11-18 — the proof was first kept in a public repository, written from private code

- **What happened:** the STUN model, its claims and its inputs were committed on a local branch of
  oopc, which is public and has no licence file; they are written from gosh, which is private and
  GPL-3.0-or-later. Nothing had been pushed.
- **Kind:** K3 (the agent put them beside the generator without asking whose code they came from).
- **Cost:** the oopc branch was rewritten without them; `prove.sh` learned to prove a class kept in
  another directory.
- **Findable by:** asking, before a file is added, where its text came from (AGENTS.md, *Stop and ask*).
- **Changed:** `CONTRIBUTING.md`: nothing written from gosh's code goes into oopc. oopc's suite has
  a loop example of its own (`Zeros`).

## 2026-11-18: the map: few of gosh's boundaries are classes, and most call the cipher

**Seen** (read, not run; gosh at `d0cfd4f`; `docs/MAP.md`): 29 places take bytes or calls from
outside. Six take them from a stranger before any key; one of those has a proved model. Most of
gosh's readers are free functions over `const char*` and a length, or a `std::string`; five are
classes with state of their own (`CounterWindow`, `ReplayWindow`, `RelayFrameParser`, `Fragments`,
`Connections`). Nearly every reader behind a key calls the cipher beside its own logic.

**What it suggests about gosh's shape:** a boundary that is to be proved as it stands needs to be a
class with private state reading a checked view of bytes, not a function over `std::string`. That
is a proposal for gosh's owner, not a change (REQ1/SHAPE-5).

**What it changed:** the queue's second domain is no longer unknown: the map recommends
`CounterWindow`, which may be provable as gosh's own text. Calls in the generator (queue item 6)
are now known to stand before most of the rows behind a key.
