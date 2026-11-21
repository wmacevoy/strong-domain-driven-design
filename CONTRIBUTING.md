# Contributing

How to work on this repository — for a new teammate and for an agent, who both arrive knowing
nothing
([SE1/A3](https://github.com/wmacevoy/software-engineering/blob/v1.7/guide/10-agents.md#a3)). A
change that makes a line here untrue updates it in the same change.

## Run it

- **Prerequisites,** all this project's own (since 2026-11-21; before, oopc's Python and a Lean
  unpacked by hand):
  - **Lean 4.36.0:** `tools/lean.sh` fetches the release into `.tools/` (about 600 MB, 3 GB
    unpacked; not committed), checked against the digest GitHub gives, and prints its path. Or set
    `LEAN` to any `bin/lean` of that version. No Lean packages are needed; the check refuses any
    other version. gosh's `tools/proofs.sh` finds it here too, when this project is beside gosh.
  - **A Python with libclang:** `pixi install` makes one in `.pixi/` (`pixi.toml`), which the
    check uses. Or set `PYTHON` to one that has `import clang.cindex`.
  - **A C++ compiler** (`c++`, C++17).
  - **For the whole check, gosh beside this project** (`../gosh`, or set `GOSH`), built once
    (`tools/build.sh` there): its proofs are run by this prover, and the lint reads mosh's core.
- **Build, run:** there is nothing to build or run but the check.
- **Reset to a known state:** `rm -rf build prover/build` — everything in them is rebuilt by the check.

## Check it

- **While working:** `tools/check.sh --lite`: the prover's own tests alone (about ten minutes).
- **The full check:** `tools/check.sh`: the prover's own tests, then gosh's proofs by this prover
  (`../gosh/tools/proofs.sh`, with `PROVER` set to `prover/` here and what it writes in
  `build/gosh`): every domain of gosh proved, the lint of all of gosh, each domain and rule broken.
  No CI yet.
- **Success prints:** `check: PASS`
- **Instruments, and how to see each fire:**
  - the audit of the claims: `prover/test_prooc.py`, which runs claims files made to cheat;
  - gosh's proofs: gosh's `tools/proofs-red.py` breaks each of its domains and rules, and each
    proof fails or the program is refused;
  - the check's own start: run it with `PYTHON=python3`, and it says `check: cannot start`.
- `./se --doctor` says what the repository lacks.

## Rules for this repository

- **gosh is read, never changed from here.** What a proof finds about gosh is a finding and a
  proposal here; the change is made in gosh, by its owner (REQ1/SHAPE-5).
- **Nothing written from gosh's code goes into oopc.** gosh is private and GPL-3.0-or-later; oopc is
  public. Files written from gosh carry gosh's copyright line.
- **`gen/` is generated, never edited.** It is committed so that what is owed can be read.
- **A claims file is trusted for nothing,** and is a program: do not check one from a stranger
  outside a sandbox.
- **"Proved" names the model, the statement and the assumptions,** every time it is written.
- **The prover is in `prover/`,** with its own suite (`prover/test_prooc.py`, about ten minutes): run it when the prover changes. It came from oopc's branch `explore/proof-compiler` at 7cb1eee on 2026-11-19, and is changed here now. This is its home: gosh carries a copy in `tools/prover/` (taken at 0744065), and takes a change from here once this check, which runs gosh's proofs by this prover, passes.
- **gosh's proofs are gosh's** (since 2026-11-21): each stands beside its class under gosh's
  `src/strong`, and gosh's own check runs them. What is learned from them about how to write code
  that is easy to reason about and prove is written here, in `docs/STRONG_DOMAINS.md`.
- A change in a requirement's meaning is a new version, and only the owner accepts one. The
  requirements are a draft until he has.
- Nothing is pushed, and no repository is made on GitHub, until the owner says.

## What AGENTS.md's words mean here

| AGENTS.md says | In this repository |
| -------------- | ------------------ |
| the repository guide | `CONTRIBUTING.md` |
| the queue | `docs/QUEUE.md` |
| findings | `docs/FINDINGS.md` (and, for the prover until 2026-11-19, `prover/FINDINGS.md`) |
| the check command | `tools/check.sh`; success prints `check: PASS` |
| the handoff check | none yet: *After a gap* in AGENTS.md, loaded at every start, and `se --post` |
| `Non-goals`, `Scope decisions` | sections of `docs/REQUIREMENTS_v1.md` |

## Done

The list in the guide's [CHECKLISTS](https://github.com/wmacevoy/software-engineering/blob/v1.7/CHECKLISTS.md#working),
and here also: a domain is not called proved until its bundle exists, its red cases have been seen
to fail, and the map says what is and is not shown.

## Where things are

- **Working set:** `docs/` — `REQUIREMENTS_v1`, `DESIGN_v1`, `QUEUE`, `FINDINGS`
- **How to develop this way:** `docs/STRONG_DOMAINS.md` — the shape, and 41 guidelines (a draft).
- **Agents:** read `AGENTS.md` (a copy of the guide's, v1.7, unedited) and this file before acting.
