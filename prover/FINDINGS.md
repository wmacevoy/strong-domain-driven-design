## 2026-11-19 — a lint before the proofs: what a proof takes as given, looked for in the program

**Asked:** "do the reference rules hold up without changing code? (references are as-if single
threaded for the duration of the reference, distinct parameters are never aliases)", then "the lint
step is part of a full compile: c++ compile, lint, prove. add lint steps that simplify proving,
such as domain boundaries. in the end proofs should only need to work out the correctness of a
domain." (the client)

**Seen** (run): `prover/lint.py` refuses a program in which a call of what is proved is
handed one thing as two arguments, or its own object; in which a thread is started; or in which
code that is not proved takes a proved value's address, casts it, or puts it in a union.
`test_prooc.py` breaks a small program thirteen ways and sees each: nine refused or accepted as
they should be, three said and not refused (an argument that is not a name, a pair in code that is
not proved, a signal handler), one file that cannot be read. On a program of 143 files and 10,451
calls it took 48 s on two cores.

**Learned:** the first lint written for this, in a conversation, left out a method that hands its
own field to another of its own methods by reference, and so reported a program clean that has 26
such lines. The rule as the client said it ("distinct parameters are never aliases") is broken by
ordinary code wherever a method passes `*this` or a field of its own along. The lint first
refused only at calls of what is proved and said the rest. The client then had that program
changed ("go ahead and migrate away"): 36 lines went, by taking a parameter by value, or by giving
a class's logic an `Edge` that stands beside it in place of the class itself. So the lint now
refuses at every call of the program's own, and says only a pair handed to the system's.

**Not shown:** one thing under two names; a reference into a container that grows; a `memset` of a
struct that holds a proved value; that a signal handler touches nothing proved.

**Changed:** `lint.py`; `prove.sh` has `READ_ONLY=1`, so the rules run before anything is proved;
the README's *What is trusted* says which of its lines are now looked for.

## 2026-11-18 — the spike carries loops: the tree's rounds are the model's, by induction

- **What was asked:** "go for it: loops" (the client, 2026-11-18). It was the risk named before
  the first spike: whether the kernel can be shown, with nobody writing the proof, that the
  interpreter's loop and the generator's are the same.
- **What was built:** `Cxx.lean` has a local with a first value, `for`, `while` and the end of a
  block (its locals are gone); a loop runs for at most `fuel` rounds, as the model's does.
  `spike-tree/Climb.hpp` is the smallest class with loops (a `for` with a local of its own, a
  `while` over a parameter with a local that outlives it and a `return` after). For each loop
  `tree.py` writes a lemma, "for any number of rounds, the tree's are the model's", and its proof:
  induction on the number, then one round compared as a method with no loop is. The method's own
  theorem uses the lemma and takes the loop whole.
- **Seen** (run, `spike-tree/red.sh`, about a minute): Climb's 14 theorems are accepted in 1.2 s,
  Gauge's 12 still are; the second checker accepts them; the standard axioms and no other. 18
  breaks, each refused at the theorem that is there for it. In loops: the generator's round
  stepping by 2, going one round too far, forgetting a statement, giving a loop no rounds, and
  returning the wrong local after it; the copier's step, condition, a local's type and a dropped
  statement.
- **Kind:** the K1 that decided the approach, answered: yes, for loops of this kind.
- **What it took:** two things were found on the way. A loop must be taken whole: if the tactic
  opens `exec` everywhere it opens the rounds inside the loop too, and the lemma no longer
  matches; so `exec` is given to it one kind of statement at a time, and each loop's own rule
  comes from its class's file. And the lemma is said of the fields one by one, not of the object:
  Lean does not see `me.total + i` as a field of some object.
- **Not shown:** `break` and `continue`; a loop inside a loop; two loops in one method; a `return`
  inside a loop; arrays, views and calls; class templates. The proof's last step knows one thing
  about conditions (that `¬ (a < b)` is `b ≤ a`): other shapes of condition may need more. The
  shape of the model's loop is read from the model's text by pattern: a model written another
  way is refused, not misread. That a local which is out of scope is out of the model's loop too
  was true here and is not checked in general.
- **Cost:** half a day more. `Cxx.lean` is 262 lines, `tree.py` 257.
- **Changed:** `spike-tree/` only.

## 2026-11-18 — a spike: the generator's reading checked by the kernel, on Gauge

- **What was asked:** "prove the prover." Then, of the plan to stop the generator saying what C++
  means: "go for it: the spike on Gauge" (the client, 2026-11-18).
- **The question:** `prooc.py` (1,939 lines) writes each method's meaning as Lean text, and all
  that is owed is derived through it; it is tested by comparison and proved by nothing. Can the
  meaning be said once, in Lean, and the kernel be asked on every run that the generator's model
  is that meaning of the method's own words?
- **What was built** (`prover/spike-tree/`, a spike, not wired into `prove.sh`):
  `Cxx.lean` (199 lines): the subset Gauge needs as a tree, and `exec`, what a tree means.
  `tree.py` (175 lines): copies each method out of the compiler's reading as a tree. It gives no
  meaning to an operator and resolves no name. For each method it writes two theorems:
  `M_text`, that the tree written back as words is the method's body, word for word, against the
  compiler's own tokens; and `M_agrees`, that `exec` of the tree is the model `prooc.py` wrote.
- **Seen** (run, `spike-tree/red.sh`): for Gauge's constructor, four methods and invariant, the
  kernel accepts all 12 theorems in 0.75 s, by one tactic the same for each (`cxx_agree`) and
  `rfl`; `leanchecker` accepts them; they rest on the three standard axioms and nothing else.
  Nine breaks, each refused where it should be: the generator's model wrong four ways (`>=` for
  `>`, an assignment forgotten, a wrong literal, a weaker invariant) fails `_agrees`; the copier's
  tree wrong three ways in its words (an operator, two names swapped, a statement dropped) fails
  `_text`; wrong two ways in what has no word (a conversion to the wrong width, a conversion left
  out) fails `_agrees`.
- **Kind:** K1, answered for the smallest class: yes.
- **What is trusted after this, for Gauge:** `Cxx.lean`, 199 lines read by a person (someone has
  to say what C++ means); the compiler's tokens and its implicit conversions (`tree.py` takes a
  conversion from the compiler's tree: it has no word to be checked against); Lean. Not
  `prooc.py`'s translation, and not `tree.py`'s copying of words.
- **Not shown** (each a K1 or K2 for the next step): loops (the model has fuel; whether `simp`
  shows two recursions the same is the open risk named before the spike); arrays and views, where
  "undefined" must be said by `exec`; calls; class templates; that one wrong reading shared by
  both programs, in something with no word, would be caught (both read the same compiler's tree);
  that the generator's refusals (a public field, a pointer) are right: they are not meaning, and
  are not touched by this. A literal is decimal only. What is owed (`COwed.lean`) is still written
  by `prooc.py`: its statements are short and read by a person, but nothing checks them.
- **Cost:** half a day. Per class it would add under a second.
- **Changed:** nothing in the generator. `spike-tree/` holds the spike; whether to build on it is
  the owner's (the estimate stands: one to three weeks for the whole subset, loops the risk).

## 2026-11-18 — `bounded_checked`, and the rule for code that is not proved

- **What was asked:** "add bounded_checked -- this allows ingress into a bounded domain -> but
  creates runtime fails, an unchecked domain can only used _checked versions, a compile-time
  checked domain does not." And of who enforces it: "the compiler with the prover can. that is
  the new 'compile' step." (the client, 2026-11-18)
- **What was done:** `bounded_checked_of` (made from any number, tests, says `ok`; its number
  expects `ok`), proved once like `bounded_of`; `Tank::fill_checked`, proved to ask before it
  takes; `ingress.py`, which refuses a program whose unproved code makes a value whose constructor
  says `pre`, or calls a method that does.
- **Seen** (run): `sample/strong/outside.h`, not proved, hands `Tank::fill_checked` a
  `LevelChecked`: accepted. Making a `Level` itself: refused, with the line. Asking a checked
  number for its number: refused. `fill_checked` without its `ok` test: Tank's proof fails. The
  checked type's test without its lower bound: its own proof fails.
- **Kind:** K1; and one K4 chosen: the rule reads words, not meanings. A compiler pass would read
  meanings, and needs the whole program to compile where the prover runs.
- **A failure when the program runs ends the process** (the client, later that day: "a failed
  run-time check is a process kill with a single caller stack trace (who called this) --- not a
  catchable exception."). The agent had first made it an answer (`false`), since what comes in is
  from anyone; that was undone. `STRONG_CHECK( condition, from )` tests, says the caller's file
  and line (the compiler's `__builtin_FILE` and `__builtin_LINE`, as a default argument; g++ 12
  and 16 seen) and aborts. The checked type lost its `ok`: one that exists is within its bounds.
  What it asks of code that is not proved: to hand over only what it has itself made right.
- **And where it stands** ("strong domains are in the Strong namespace and the src/strong/...
  strong domains may not call any _checked abi", the client, the same day): `ingress.py`, given
  `STRONG=dir`, refuses a proved class outside that directory or namespace, and anything with a
  body inside it that is not proved; `prooc.py` refuses a proved method, not itself a `_checked`
  way in, that takes, makes or calls a `_checked`. Each seen refused. Suite: 49 refusals, 37 ways
  to be wrong, 10 as-is, 4 cases of the rule, PASS.
- **And by what name** ("weak domains can only call _checked versions, even if those versions
  cannot fail", the client, the same day): `ingress.py` refuses a call from code that is not
  proved to a proved function or method by any name that does not end `_checked`, and lists every
  use of one that does: all the places the two kinds of code meet. Seen refused; suite PASS (49
  refusals, 37 ways to be wrong, 10 as-is, 4 cases of the rule).
- **One K2 on the way:** inside a macro's argument the words of an operator are not where the
  library says the expression is; the generator now asks the library for the operator itself.
- **Changed:** `ingress.py` (new), `prooc.py` (`return method( ... )`; a `bool` field of a class
  template first given a condition; `given` is a word of Lean's), the samples, claims and tests.

## 2026-11-18 — `bounded<a, b, type>`: a class template proved once, of every type and bounds

- **What was asked:** "bounded<a,b,type> fixes all integer types." "go for it: bounded, proved once
  for every a and b. i think do this for uint,int,float,double --- the implied constraint on
  float/double is they are 'normal' (not nan, pm infity). this fixes the bottle." And of the
  bounds: "i think it would be [a,b]" (the client, 2026-11-18).
- **What was done:** `prooc.py` reads a class template of one type and values of that type as it
  is written. Its model is a Lean function of the type (anything with a `≤` that can be decided)
  and of the values, and each statement owed is of all of them.
- **Seen** (run): `bounded_of` (`sample/strong/bounded.h`) is proved in 30 lines that never ask
  what `≤` is: the constructor's precondition and the invariant are the same words. The model and
  the C++ agree on 8,004 lines at `uint64_t`, `int64_t`, `double` and `float`, infinities and
  not-a-number among what was tried. `Tank` takes a `bounded<0, 100, uint32_t>` and indexes 101
  places by it with no test, and makes one from `n % 101`: proved; from `n`: Tank's proof fails and
  the template's does not; a bound of -1 at an unsigned type: the compiler refuses it. Suite: 47
  refusals, 35 ways to be wrong, 10 as-is, PASS.
- **Kind:** K1, answered by building it.
- **What it means for a type like Percent:** no class and no proof of its own. The bounds are in the
  type's name, the compiler keeps them apart, and the one thing left to prove is at each place a
  number is made into one.
- **Not shown:** a class that uses the template at `int64_t`, `double` or `float`: the generator
  reads ordinary classes with unsigned numbers only, so `Bottle` (a `double` volume from 0 to its
  capacity, where "NaN is outside the contract", REQ10) is not yet read. That within finite bounds
  means finite and a number is IEEE 754's, tried and not proved. The capacity of a bottle is not
  known when it is compiled: a bound that is a value of the object is a precondition, not this type.
- **Changed:** `prooc.py` (`GenT`, `Klass.generic`, `emit_owed` written again, `needed_text`, the
  four-type comparison), `prove.sh` (C++20; `needs`), `test_prooc.py`, the two samples and claims.

## 2026-11-18 — what a caller owes, said by `pre()`, and owed by the caller

- **What was asked:** "the burden of proof moves to the caller." "contracts are proven at compile
  time - they can be ignored at run time." (the client, 2026-11-18)
- **What was done:** `prooc.py` reads C++26's `pre( condition )` on a method or a constructor. The
  method's model has no result where the condition is false, and what is owed of the method is
  owed given it. Nothing new is owed of a caller: its model calls the callee's, so its own "no
  memory error" cannot be proved unless it keeps the condition. A value of another class may be
  made inside a method.
- **Seen** (run): `sample/stats/grade.h`. `Score( raw ) pre( raw <= MOST )` tests nothing;
  `Board::mark_number` makes one from `n % 101` and is proved; with `Score s( n )` Board's proof
  fails and Score's does not. `Shelf::at( i ) pre( i < used )`; `first` calls `at( 0 )` only where
  `used` is not 0, and without that test its proof fails. A precondition that says too little for
  its own method (`i <= used`), or less than the invariant needs, fails that method's own proof.
  Suite: 43 refusals, 31 ways to be wrong, 9 as-is, PASS.
- **Kind:** K1, answered by building it. One K2 on the way: the library that reads C++ here
  (libclang 18, from Python) shows nothing of a `pre(...)`, however it is disguised (as `noexcept`
  of the condition, or as an attribute): the condition is in no part of the tree it hands over.
- **Cost:** the condition is read from a second text, `gen/C.read.hpp`: the class's own, with each
  condition written again at the head of its method's body. That is one more thing trusted (the
  README says which), and the first place where what is read is not, character for character,
  what is compiled.
- **Not shown:** a precondition that reads an array or calls; one kept across classes other than a
  constructor's; that g++ 16 reads the same condition the same way (it compiles `pre`, and the
  comparison here is compiled with `pre` as a macro instead).
- **Changed:** `prooc.py` (`with_pre`, `pre_def`), `prove.sh` (the read text in the bundle),
  `test_prooc.py`, the sample and its three claims files, the README.

## 2026-11-18 — what a caller owes, said by a type and proved

- **What was asked:** "can't that be part of the type? it doesn't have to be checked; it just has
  to be proven." (the client, 2026-11-18), of a method that was right only for numbers below a
  bound its caller happened to keep.
- **What was done:** a parameter may be a value of another class read here, and a constructor may
  take arguments. What is owed of the method assumes that class's invariant of the value; that
  class's own proof shows its constructor establishes it, whatever it is given.
- **Seen:** `Percent` (at most 100, made by a remainder) and `Dial`, which indexes 101 places by
  one with no test (`sample/stats/dial.h`). Both proved. A constructor that lets 101 through fails
  `Percent`'s proof; a `Percent` that says "at most 101" is proved, and `Dial`'s proof fails; a
  `Dial` of 100 places fails. A class named before the type it uses is refused.
- **Trusted, as before:** that nothing reaches a value's bytes past `private` (a cast, a stray
  write). That is what makes "only its constructor makes one" true.
- **What it changed:** the subset in the README; 40 refusals and 26 ways to be wrong.

## 2026-11-18 — a pointer and its length, and a function that is not a method

- **What was asked:** the next piece after reading a class where it stands: most code that reads
  bytes takes `const char* data, size_t len`, and much of it is not a method.
- **What was done:** a pointer to const bytes with an unsigned 64-bit parameter next after it is a
  view, the same one `Bytes` is in the model: `p[i]` is a read, owed to be below the length. Signed
  bytes are read through a `const unsigned char*` local made once from the parameter. A function
  is read as a class with no state.
- **Seen:** `frame_begins` (a function over `const char*`) and `Checksum` (a method) in
  `sample/wire/frame.h` are proved where they stand; each fails with its bound off by one.
- **Not shown, and trusted:** that the pointer does point to that many bytes. Nothing in the
  callee can show it.
- **Limits met:** a function gives back one number: no reference parameter, so a function that
  fills a struct is not read. A class named `Sum` clashed with Lean's own `Sum`.
- **What it changed:** the subset in the README; 38 refusals and 22 ways to be wrong.

## 2026-11-18 — a class is read where it stands: no model written by hand

- **What was asked:** "the goal is the generator can generate the model --- ow the model must be
  audited each time as well." (the client, 2026-11-18). A class of another program had been
  written again in the subset, by hand, statement for statement. That second text is trusted
  exactly as the claims are not.
- **What was done:** `prove.sh` reads `from/C`, a path under `SUBJECT`, and the generator takes the
  class's own text from that file. To read ordinary C++ as it is written it learned: calls to the
  class's own methods, private ones among them; `bool`; `/` and `%`; `static const` numbers; an
  initializer list; `+=` and its kin, `++`; `memset` of a whole array. A class that cannot be
  changed may say no invariant.
- **Seen:** `Histogram` (`sample/stats/histogram.h`, a file that does not compile alone, with
  another class and a global beside it) is proved, 10 statements, and three broken versions fail.
  The four earlier examples generate the same text as before, character for character. Writing
  the sample, the proof refused it once: `count / (total / parts + 1)` divides by zero when
  `total` is 2^32-1 and `parts` is 1.
- **Not shown:** that a class means alone what it means in its file (README). A function that is
  not a method, and a pointer with a length, are not read: most parsers are written that way.
- **What it changed:** the subset and "Another program's classes" in the README; 33 refusals and
  20 ways to be wrong in the suite.

## 2026-11-18 — a shift by an amount known only when it runs

- **What was asked:** a class from another project that keeps a set of bits in words, and tests and
  sets one by `word >> (n & 63)`. The generator refused it: only a shift by a literal was read.
- **What was done:** such a shift is now read, as `Prooc.shl` and `Prooc.shr`: `none` at the width
  or more, where C++ leaves it undefined. So what is owed of a method includes that every shift is
  defined, with no new kind of statement. A signed amount is refused, and so is such a shift in
  the invariant. `Bits` is this repository's example; with `n & 127` its proof fails (seen).
- **What it changed:** the subset (README); 30 refusals and 17 ways to be wrong in the suite.

## 2026-11-18 — the spike: what is owed came from the C++ alone, and the proofs became hints nobody trusts

**What we expected.** That the spike already kept the statements (generated) apart from the proofs
(by hand), so that an agent could write proofs and a person need read only the statements.

**What happened.** It did not, in two places, and both were found by asking what a claims file
written to cheat could do, rather than by any test:

- **The invariant was in the claims.** The file nobody was to trust said what every statement was
  about. It is now the class's own `bool invariant() const`, read by the generator, and compared
  with the C++'s own answer after every call of the comparison.
- **The generated statements imported the claims,** and took proofs "by name". So the claims'
  notations, instances and macros were in force while the statements were read: a claims file
  could change what they meant, or what `#print axioms` printed. Now what is owed is one generated
  statement, `C.Owed`, in a file that imports nothing written by hand, and it is compiled first.

With the claims untrusted, three more ways to cheat had to be closed. Each is a case in
`test_prooc.py`, seen refused:

- `native_decide`, and `bv_decide` which uses it, trust compiled code, and a claims file can swap
  compiled code for its own. The audit allows only the three standard axioms. The STUN parser's two
  lemmas by `bv_decide` were proved again without it: 40 lines for 2.
- A claims file can switch Lean's kernel off (`debug.skipKernelTC`) and add a theorem named `owed`,
  of the right statement, with no proof of it. It compiled, and the audit passed it. `leanchecker`, which ships
  with Lean, has the kernel check the compiled file again, and refused it.
- Lean runs a claims file's commands while it checks it, so one could write over the compiled
  statement it is checked against. `prove.sh` compares those files before and after. It does not
  stop a claims file doing anything else to the machine.

A loop's bound stopped being part of any statement: what is owed is "for some number of rounds
there is a result", and the number is a hint.

**What changed.** `prover/`: `prooc.py` (reads `invariant()`, writes `COwed.lean`, no
`CCheck.lean`), `Audit.lean` (new), `prove.sh`, the three models and their claims, `test_prooc.py`
(29 refusals, and ways to be wrong in the C++, in the claims, and in the generator), `README.md`. On the branch
`explore/proof-compiler` only. Not changed: the generator's reading of the C++ is still tested, not
proven, and is now the largest thing trusted; calls between methods are still refused, so "it makes
correct calls" is not yet something the generator can derive.

Afterwards the STUN parser's model, proofs and inputs were taken out of this repository, since they
are written from another project's code: `prove.sh` takes a `DOMAIN` directory, and they are kept
in a private project that has this one as a subproject. `Zeros`, a loop over a byte view, was added
here so that loops and the view are still proved and seen red in this repository's own suite.

## 2026-11-17 — the spike, with loops and a byte view: a STUN parser proved

- **What was asked:** "add loops and a byte view, try the STUN parser" (the client, 2026-11-17), after
  the entry below. On the branch `explore/proof-compiler`, not pushed.
- **What happened:** `prooc.py` now reads `while` and `for` (with `break` and `continue`), a `Bytes`
  parameter (a pointer and a length, read by `at()` and `size()`), shifts, and `&&` and `||` whose
  right side reads memory. `model/StunAnswer.hpp` is the logic of a real parser of STUN answers, 137
  lines, with one loop over attributes and four loops inside it. Lean 4.36 checks, for every
  sequence of bytes of any length, that `parse` ends, reads and writes nothing out of bounds, and
  never keeps an IPv6 address of one link alone. 376 lines of claims and proofs, 9 seconds.
- **It is the parser it was written from, as far as tests say:** the original function, the class,
  and the Lean model print the same on 15,500 seeded calls and on the original's fuzzing corpus.
- **Seen red:** the bounds test on an attribute's length removed; 4 bytes taken for 20; 17 bytes
  copied into 16; a loop that does not move on; `fd80` tested where `fe80` is meant. Each fails
  the proof it should. 25 refusals; `test_prooc.py`, about 90 seconds.
- **What it took, in order:**
  1. *A loop needs a number.* It became a function that gives `none` when a stated number of
     rounds is not enough; the claims name the number, and one theorem then says the C++ ends and
     is safe. Proofs about a loop are by induction on the rounds left, with the loop's invariant
     written by hand.
  2. *One function was too large to reason about.* Lean's simplifier ran out of time on the round
     of the outer loop (about 40 reads, 8 paths). The generator now makes a function of each
     branch of more than one statement, and a loop hands back only what it changes. After that,
     each piece's proof takes under a second. **This is the finding:** what is generated must be
     shaped for the proof, in small pieces with a lemma each; a model that only means the right
     thing is not enough.
  3. *Values need names.* Proofs had to name what the simplifier had spread through the goal (an
     attribute's size, read from two bytes), by writing the term out. That is the brittle part:
     a change in the C++ changes the terms.
- **What it does not show:** as the entry below; and here, that the class is the original parser
  (tested, not proven), IPv4 in IPv6's form (tested), anything of the port. Two lemmas rest on
  `bv_decide`, which trusts Lean's compiled code as well as its kernel.
- **Not to be pushed as it is:** `model/StunAnswer.hpp`, its claims and its script are written from
  a private project's code, under its licence. This repository is public and states no licence.
  They belong in that project; the generator and `Gauge` and `Tally` are this one's.
- **Kind:** K1, answered: loops and a byte view took a day of an agent's work, not months, for one
  parser. What is still K1: calls between methods (so that a proof can be cut where the C++ is),
  and how the proofs wear when the C++ changes.
- **Changed:** nothing in the requirements or the queue.

## 2026-11-17 — a spike: a C++ class read into Lean, and what must be proven of it

- **What was asked:** whether a domain can be *proven to be applied*, so that reasoning is about the
  domain and its boundary and not the program; and whether a generator could write "what needs to
  be proven", for something like Lean, and break on any break of the boundary (the client,
  2026-11-17: "try the spike, be flexible"). Not a requirement yet; on the branch
  `explore/proof-compiler`, in `prover/`.
- **What happened:** it works for two small classes. `prooc.py` (libclang, about 590 lines) reads
  `Gauge` (a `SizedBottle` of whole numbers) and `Tally` (which indexes an array), refuses a class
  whose state could be reached from outside, and writes each method as a Lean function that gives
  `none` for a read or write outside an array. It also writes the statements owed: every method is
  safe from any state satisfying the invariant, and keeps it. The invariant and the proofs are
  written by hand in `claims/`; Lean 4.36 checks all 18 in under 3 seconds, with no bound on history
  and no packages, resting on Lean's three standard axioms. The model and the C++ agree on 2,000
  seeded calls each.
- **Seen red** (`test_prooc.py`): 20 refusals (a public field, a friend, a pointer out, a global, a
  field left unassigned, signed arithmetic, ...). The C++ losing a clamp, indexing with three bits
  for two, or dropping a bounds test: the proof fails. A proof replaced by `sorry`, removed, or
  proved of something weaker: what is owed does not compile. The generator made to translate
  wrongly: the proofs still pass and the comparison with the C++ fails.
- **What it does not show:**
  - *The model is the C++.* Tested by the comparison, not proven.
  - *The invariant is the right one.* `Inv := ... ∨ True` is proved as readily. The reader must read
    the invariant and the claims; the tool cannot judge them.
  - *Nothing else reaches the state.* `private` is the compiler's rule: a memory error elsewhere in
    the program, or a cast of the object, goes past it. Each domain proven free of memory errors
    closes this only when every domain in the process is.
  - *Loops, calls, byte views, bases, `virtual`.* All refused. A loop needs a written reason it ends
    and its own invariant; not tried.
- **What it cost to write the proofs:** `Gauge`'s ten went through nearly as first written.
  `Tally`'s eight took four rounds, none about the mathematics: Lean's simplifier rewrote the index
  into a form the proof had to match, and a primitive defined with a dependent `if` could not be
  generalized over until it was given two lemmas (`Prooc.get_of_lt`, `set_of_lt`). So the primitives
  must be designed to be reasoned about, with lemmas, and proofs should name them, not unfold them.
- **Against the model checker (`proof/`):** CBMC cannot read C++ at all, and needs a bound or a
  hand-written inductive harness; but it reads real C with no model to trust, and finds
  counterexamples by itself. Here the claims are a page a person reads and the history has no bound,
  but a failed proof says only that it failed.
- **Kind:** K1 — a question, answered for the smallest case; the loops are still K1.
- **Changed:** nothing in the requirements or the queue. If it is wanted: a queue item for loops and
  a byte view, which is what a real parser needs, would say whether this is weeks or months.

