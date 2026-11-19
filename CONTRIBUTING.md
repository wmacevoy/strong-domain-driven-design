# Contributing

How to work on this repository — for a new teammate and for an agent, who both arrive knowing
nothing
([SE1/A3](https://github.com/wmacevoy/software-engineering/blob/v1.7/guide/10-agents.md#a3)). A
change that makes a line here untrue updates it in the same change.

## Run it

- **Prerequisites:**
  - **Lean 4.36.0**, unpacked at `.tools/lean-4.36.0-linux/` (not committed, 3 GB), or anywhere,
    with `LEAN` set to its `bin/lean`. It is the release `lean-4.36.0-linux.tar.zst` from
    <https://github.com/leanprover/lean4/releases/tag/v4.36.0>. No Lean packages are needed. The
    check refuses any other version.
  - **A Python with libclang** (`import clang.cindex`), named by `PYTHON`. The system's `python3`
    here has none. oopc's pixi environment has one: in a checkout of oopc, `pixi install`, then
    `PYTHON=/path/to/oopc/.pixi/envs/default/bin/python`.
  - **A C++ compiler** (`c++`, C++17).
  - **A gosh that has been built** (`tools/build.sh` there, once): the lint reads every file of
    gosh's `src`, and they include mosh's core and its `config.h`, in gosh's `.build/core`.
    And, if it is there, g++ 16 in gosh's `tools/gcc16/.pixi` (`. tools/gcc16.sh` on gosh's
    `strong/main` fetches it): what is proved is then also compiled with contracts. Without it
    the check says so and goes on.
- **Build, run:** there is nothing to build or run but the check.
- **Reset to a known state:** `rm -rf domains/*/build` — everything in it is rebuilt by the check.

## Check it

- **The full check:** `tools/check.sh` (about three minutes): it compiles what is proved, lints all of gosh's `src`, proves each domain, and breaks each. No CI yet: the check needs Lean (3 GB), a Python with libclang, and a built gosh beside it.
- **Success prints:** `check: PASS`
- **Instruments, and how to see each fire:**
  - the proofs: `tools/red-test.py` breaks each domain's text (for a class read from gosh, a copy of gosh's file), fifteen ways in all, and each proof fails; and breaks gosh against each rule (three ways), and the program is refused;
  - the audit of the claims: `prover/test_prooc.py`, which runs claims files made to cheat;
  - the check's own start: run it with no `PYTHON` set, and it says `check: cannot start`.
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
- **The prover is in `prover/`,** with its own suite (`prover/test_prooc.py`, about ten minutes): run it when the prover changes. It came from oopc's branch `explore/proof-compiler` at 7cb1eee on 2026-11-19, and is changed here now.
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
- **How to develop this way:** `docs/STRONG_DOMAINS.md` — the shape, and 33 guidelines (a draft).
- **Agents:** read `AGENTS.md` (a copy of the guide's, v1.7, unedited) and this file before acting.
