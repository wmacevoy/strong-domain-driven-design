# Requirements — v1

What must be observably true, and what is not being built. Changes only with the client; a change in
meaning is a new version (`REQUIREMENTS_v2.md`); a spelling or lint fix is not. See
[SE1/R1–R11](https://github.com/wmacevoy/software-engineering/blob/v1.7/guide/04-requirements.md).

Client: Warren MacEvoy, who is also the owner of gosh and of oopc · Date sent: 2026-11-18 ·
*Tell us what is wrong with it.*

**A draft.** Written by Claude Fable 5.2 from what the client said on 2026-11-17 and 18, in the
sessions where the spike was made. The client's words are quoted; everything else is the agent's
reading, and is marked *(inferred)* until the client confirms it. Nothing here is accepted yet.

## Glossary

| Term | Meaning |
| ---- | ------- |
| the subject | gosh, the program whose boundaries are being proved. Private; read here, never changed from here |
| domain | a part of the subject with state of its own, written as a C++ class whose fields are all `private` |
| boundary | the public methods of a domain: the only way in to its state |
| invariant | what a domain says is always true of its state: its own `bool invariant() const` |
| model | what the generator writes from a domain's own code: each method as a function, in Lean. Generated, never written by hand *(the client's word, 2026-11-18)* |
| rewrite | the subject's code written again by hand so that the generator can read it. One more text to audit: allowed only until the generator reads the code itself, and always named as one *(inferred)* |
| the generator | `oopc/cpp-proof-gen/prooc.py`: reads a domain's code, refuses a boundary that leaks, and writes the model and what is owed |
| owed | the one statement generated from a model: no method commits a memory error, every loop ends, and every method leaves the invariant true |
| claims | a proof of what is owed, written by a person or an agent. Trusted for nothing |
| the audit | what is asked of compiled claims before they count: a theorem of exactly what is owed, on the standard axioms only, accepted by the kernel when asked again |
| assumption | something the proof rests on and does not show (a K4, [SE1/U4](https://github.com/wmacevoy/software-engineering/blob/v1.7/guide/02-unknowing.md#u4)): named, never silent |
| the product | the bundle a proved domain leaves: hashes of the texts, Lean's version, what the audit found |
| the map | the list of the subject's boundaries: each proved, assumed, or not yet looked at |

## Mission

- **MISSION-1** *(since v1)* *(judged)* "the goal is to learn from proving the boundaries of gosh,
  which might change its shape." *(client, 2026-11-18)* Judge: Warren MacEvoy, on the findings and
  the map, whenever a domain is finished. Veto: a proof that says more than it shows.

## Fundamental shape

Held by: Warren MacEvoy. The holder proposes a change; the client makes it, in a new version.

- **SHAPE-1** *(since v1)* *(judged)* **What is owed comes from the code, and nothing else.** "What
  needs to be proven needs to be derived from the code. Hints on the proof can be guided, but it must
  be automatically auditable against the code." *(client, 2026-11-18)* C++ is the source, and
  `private` is the boundary: "privacy controls boundaries as well, so boundaries are easier to
  reason about." *(client, 2026-11-17)* And the code is the subject's own, where it stands: "the goal is
  the generator can generate the model --- ow the model must be audited each time as well."
  *(client, 2026-11-18)*
- **SHAPE-2** *(since v1)* *(judged)* **The product is the proof.** "the product is the proof."
  *(client, 2026-11-17)* The generator writes what must be proven, "or break[s] on any domain
  boundary break"; it writes nothing that ships.
- **SHAPE-3** *(since v1)* *(judged)* **Security first, correctness second; memory errors by
  domain.** "The goal here is proof of security (first) and proof of correctness (second)."
  "the point is to control memory error by domain, and then the memory error is proved in every
  domain. (except ssh and mosh core in this case, which is exactly where we want it)." *(client,
  2026-11-17)*
- **SHAPE-4** *(since v1)* *(judged)* **Assumptions are named.** "k4: the compiler is correct, the
  machine is correct, it is called correctly. derive: no memory corruptions, it makes correct calls,
  etc." *(client, 2026-11-18)* What is assumed is listed where the proof is, and nothing else is.
- **SHAPE-5** *(since v1)* *(judged)* *(inferred)* **This project learns; gosh decides.** What a
  proof finds about gosh's shape is written here as a finding and a proposal. A change to gosh is
  made in gosh, by its owner, under gosh's own requirements.
- **Foundation:** SE1.7
- **Says no to:** generating C to prove ("The gen would not generate C", client, 2026-11-17);
  trusting the text of a proof because of who or what wrote it; a claim of "proved" with an
  assumption left out.
- **Exceptions:** none.

Judge of each: the holder, when a domain is finished.

## The pain

In the client's words *(2026-11-18; the figures are as the client heard them, and are not checked)*:
"white hat agents can write code at an unauditable pace". "The agents against you means this must be
done, because any flaw will be found and exploited." "A number I heard is now 5 hours between an
exploit being discovered and it being deployed. By next year it will be 1 hour, and the correct
security model is 0 --- nothing is deployed that cannot be proven secure before full contact."

gosh reads bytes from anyone on the Internet, on a machine its user logs in to. Today its
boundaries are tested and fuzzed, and none is proved.

## People this touches

- **The client,** who owns gosh, oopc and this project, and reads every statement that is called proved.
- **gosh's users** (students, on machines they do not administer), who are never in the room: a flaw
  at a boundary is theirs to suffer.
- **gosh's reviewer,** not yet named (gosh's queue), who would read a map and a bundle instead of the code.
- **Agents,** who write claims, and are trusted for none of them.

## Requirements

- **DOM-1** *(since v1)* *(inferred)* Each domain taken from the subject is named under `domains/`
  with its claims, and the check proves it: it prints `PROVED` and the domain's name, and leaves
  the product. The model is generated from the subject's own file, read where it stands when the
  check runs (SHAPE-1).
- **DOM-2** *(since v1)* *(inferred)* Where a domain is still a rewrite, the map says so in those
  words, and the rewrite is compared with the subject's own code in the check: the same inputs to
  both, the same answers. Until it is, the map says "a rewrite is proved; that it is gosh's code is
  not shown here". A rewrite is a debt in the queue, not a way of working.
- **DOM-3** *(since v1)* *(inferred)* The check says which commit of the subject it read, and
  whether the subject had changes not committed; the product names the file, its hash and that
  commit. A rewrite names the commit it was written from, and the check says so when the subject's
  file has changed since.
- **RED-1** *(since v1)* *(inferred)* For each proved domain, the check breaks the model in the ways
  its proof is there to prevent, at least one for each thing owed, and sees each proof fail.
- **AUD-1** *(since v1)* Claims that cheat do not count: an axiom of their own, a proof left out, a
  proof by compiled code, a theorem of another statement, a proof the kernel was told not to check.
  Each is refused, and is seen refused. *(This is the generator's own suite, in oopc.)*
- **MAP-1** *(since v1)* *(inferred)* The map lists every boundary of the subject where bytes or
  calls come in from outside it, and for each: proved (and of which model, at which commit), assumed
  (and why), or not yet.
- **LRN-1** *(since v1)* *(inferred)* Every domain attempted, proved or not, ends in a finding that
  says what it suggests about the subject's shape, and what it cost: lines of model, lines of
  claims, and how much of the claims a change to the model made untrue.

## Inputs: absent, late, wrong, lying

| Input | Absent | Late | Wrong | Lying |
| ----- | ------ | ---- | ----- | ----- |
| a model | the check fails, naming it | — | outside the subset, or a leaking boundary: the generator refuses, with the line | an invariant that says too little still proves: the invariant is read by a person (it is a few lines of the C++) |
| claims | the check fails | — | a proof that does not hold: Lean refuses | made to cheat: the audit refuses (AUD-1) |
| Lean | the check refuses to start, and says where to get it | — | another version than the one pinned: the check refuses to start | a broken kernel: not found here; it is an assumption |
| the generator (oopc) | the check refuses to start | — | a wrong reading of the C++: found only where the comparison reaches | the same |
| the subject's source | the check refuses to start, and says where it looked | — | no longer in the subset: the generator refuses, with the line; a line a red case breaks is gone: that case fails, and says so | changed since a rewrite was written: DOM-3 |

## Operating envelope

- **Scale:** the subject's boundaries: tens, not hundreds *(invented)*. Not designed for a program
  that is not written as domains.
- **Speed:** the check in under 5 minutes on the client's server *(invented)*; one domain's proof in
  under a minute, so that a fix can be proved again in the time it takes to write it.
- **Recovery:** nothing runs. Everything but the sources is rebuilt by the check.
- **Availability, resources, interruption:** not applicable; the check is safe to stop at any instant.

## Security, law, and ethics

- No data about people is collected or kept.
- The subject is private, and is GPL-3.0-or-later (its `LICENSE-GOSH`). A model written from it is
  a derived work: it is kept here, in a private repository, with the subject's licence line, and
  never in oopc, which is public. *(agent's reading; the client decides)*
- A claims file is a program: Lean runs what it says while checking it. Claims from a stranger are
  checked in a sandbox, or not at all.
- "Proved" is a strong word. Each use of it here names the model, the statement and the assumptions.

## Assumptions (K4s), read back to the client

- "The compiler is correct, the machine is correct, and the domain is called correctly." — the
  client's own, 2026-11-18.
- "We're assuming every part of a program is either a proved domain or on the list of what is
  assumed, since a memory error anywhere else goes past `private`. True?" — not yet answered.
- "We're assuming the generator's reading of C++ may be trusted where the comparison has reached,
  until it is itself proved or replaced. True?" — not yet answered.
- "We're assuming Lean's kernel, its library and its three standard axioms. True?" — not yet answered.
- "We're assuming a model may be gosh's code written again in the subset, rather than gosh's code
  itself, for as long as this project is learning. True?" — answered, 2026-11-18: no. "the goal is
  the generator can generate the model --- ow the model must be audited each time as well."
- "We're assuming a class means alone what it means in its file: the generator reads the class's
  own text with only the standard headers before it. True?" — not yet answered.
- "We're assuming a class of gosh's that says no invariant claims nothing of its state, since it
  cannot be changed from here. True?" — not yet answered.

## Scope decisions

- The subject is gosh alone — the mission names it.
- Lean 4, one pinned version — the spike used it, and its checker ships with it. *(inferred)*
- The generator lives in oopc, and this project uses it as a subproject — client, 2026-11-18.

## Non-goals

- Not changing gosh from this repository — SHAPE-5.
- Not proving ssh, mosh's core, the cipher or the kernel — they are assumed, and that is "exactly
  where we want it" (client, 2026-11-17).
- Not a verifier for C++ in general — only for code written as domains, in the subset.
- Not proving the compiler or the machine — SHAPE-4.

## Not yet answered

Guesses nobody has agreed to.

- Does a proved model replace the subject's code, so that gosh ships what was proved? — the client.
- Does Lean become part of gosh's own check or CI? — the client.
- oopc has no licence file, and the generator is on a branch there that is not pushed. When is it
  pushed, and under what licence? — the client; on 2026-11-18: "do not push oopc".
- Is this repository hosted, and where? — answered by the client, 2026-11-18: "yes, make the
  private repo". It is private, on GitHub.
- Which boundary of gosh is next? — the client, from the map.

## Deferred

- Not yet: calls from one domain to another, so "it makes correct calls" cannot be derived — the
  generator refuses calls; it is the next piece of the generator.
- Not yet: a proof that the generator reads C++ rightly — it is tested by comparison only.
- Not yet: CI — the check needs Lean (3 GB) and a submodule commit that is not on GitHub.
