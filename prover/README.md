# prover — a spike: C++ is the source, and the product is a proof

*(2026-11-17 and 18, on the branch `explore/proof-compiler`. A spike, not a requirement: nothing in
`docs/REQUIREMENTS` asks for it yet. What it found is in `docs/FINDINGS.md`.)*

`cpp-inv-gen/` reads C++ and writes C. This reads C++ and writes **what must be proven of it**,
for [Lean 4](https://lean-lang.org), and refuses a class whose boundary leaks. Nothing it writes ships.

**What is owed is derived from the C++ alone**: the methods, and the class's own
`bool invariant() const`. The proofs are hints. A person or an agent writes them, nobody trusts
them, and an audit checks them against what the C++ owes.

```sh
LEAN=/path/to/lean pixi run ./prover/SUBJECT=prover/sample prove.sh Gauge Tally Zeros Bits Ration Fuse Histogram frame_begins Checksum Percent Dial Score Shelf Board bounded_of bounded_checked_of Tank   # generate, check, audit, compare (10 s)
LEAN=/path/to/lean pixi run python prover/test_prooc.py                # 49 refusals, 37 ways to be wrong, the rule for code that is not proved (9 minutes)
```

| | |
|---|---|
| `model/*.hpp` | the input: ordinary C++, which knows nothing of this tool. `Gauge`, `Tally` (an array), `Zeros` (a loop over a byte view), `Bits` (a shift by an amount known only when it runs), `Ration` (a method that throws) and `Fuse` (one that ends the process) |
| `from/C`, `sample/` | a class read **where it stands** in a file of another program: `from/C` is one line, the file's path under `SUBJECT`. `Histogram` is the example, in a file that does not compile alone; `frame_begins` (a function) and `Checksum` take a pointer and its length; `Dial` takes a `Percent`, and relies on what that type says |
| `model/Bytes.hpp` | the byte view, a pointer and a length: the one way a model reads memory that is not its own |
| `prooc.py` | the generator |
| `Prooc.lean` | the primitives a model touches memory by, and how a loop says what happened; written by hand, once |
| `gen/CModel.lean` | generated: each method as a function, or `none` for a memory error; and the invariant, from `invariant()` |
| `gen/COwed.lean` | generated: **what is owed**, one statement, `C.Owed`. It imports the model and nothing written by hand |
| `claims/CClaims.lean` | by hand (or an agent): the proofs, ending in `C.Claims.owed`, a proof of `C.Owed`. Trusted for nothing |
| `Audit.lean` | written by hand, once: what is asked of a compiled claims file before it counts |
| `gen/CDiff.lean`, `gen/C_diff.cpp`, `gen/C.script` | generated: the model and the C++ run on the same seeded calls |
| `scripts/C.py` | by hand, if the seeded calls would not reach far: more calls for the comparison |
| `build/C.bundle` | the product: hashes of the texts, Lean's version, what the audit found, and the axioms the proof rests on |

## Its parts

Each answers for one thing (the client, 2026-11-19: "think about domain based design for the
prover ... it will get too big to reason about too"). One boundary matters more than the rest:
**what was read, as data.** Before it, Clang; after it, functions from data to text.

| Part | Answers for | Asks Clang? | Refuses? |
| ---- | ----------- | ----------- | -------- |
| `clang_edge.py` | finding Clang's library, and the one question its binding does not answer | yes | no |
| `reader.py` | a class of the subset, read into `cxx`: every rule of the subset is here | yes | yes |
| `cxx.py` | the tree, as plain data; where `spike-tree/Cxx.lean` names a node, the same name | no | no |
| `model.py` | the tree, as the model in Lean | no | no |
| `owed.py` | the tree, as what must be proved | no | no |
| `compare.py` | the tree, as the two programs and the script that compare model and C++ | no | no |
| `subject.py` | a class where it stands in another program: its text, and `pre(...)` at the head of the body | yes | yes |
| `proofs_reader.py`, `proofs.py` | a proof file read into the tree; and what is owed of it | the reader | the reader |
| `lint.py`, `rules/` | the command, and one file per rule, each with its own state | yes | the rules |
| `ingress.py` | the rule between proved and unproved code, by words | no | yes |
| `prooc.py`, `prove.sh`, `judge.sh` | the commands: read then write; the order of the steps; and that nothing written has changed by a byte | | |
| `spike-tree/tree.py` | the same tree, as Lean data the kernel checks against the model and the source's words | no | says what it does not reach |

`sh judge.sh` proves the prover's own 20 classes and fails if a generated file differs from what
is committed: run it after any change here, then `test_prooc.py`.

## The four things it does

1. **Refuses a leaking boundary.** A class is a domain only if nothing outside can reach its state.
   Refused: a field that is not private, a friend, a base, a pointer or reference anywhere, the
   address of anything, a global beside the class. And what has no exact meaning here: signed
   arithmetic (overflow is undefined), a field the constructor leaves unassigned, a local with no
   first value.
2. **Says what is owed.** For every method: it commits no memory error from any state that satisfies
   the invariant, and it leaves the invariant true (or, if `const`, the state unchanged). With "a new
   object satisfies it", that is induction over every history, with no bound. The invariant is the
   class's own `bool invariant() const`, one `return` of a condition on the fields: a class that
   has none is refused, and one that claims nothing says `return true;`.
3. **Audits the proof, as something nobody trusts** (`prove.sh`, `Audit.lean`):
   - what is owed is compiled before the claims are looked at, and the compiled files are compared
     after, since Lean runs what a claims file says while it checks it;
   - the claims are never read as text again. Of their compiled form: `C.Claims.owed` is a theorem,
     of exactly `C.Owed`, the generated one;
   - everything it rests on, followed to the end, uses only `propext`, `Classical.choice` and
     `Quot.sound`. So no `sorry`, no axiom of the claims' own, and no `native_decide` or
     `bv_decide`: those trust compiled code, which a claims file can swap for its own;
   - Lean's kernel checks every declaration of the claims again (`leanchecker`), which finds a
     proof put in with the kernel switched off.
4. **Compares the model with the C++.** The proofs are about the model. That the model is the C++
   is tested, not proven: the same calls to both, and after each call the result and whether the
   invariant holds, which the C++ computes with its own `invariant()`.

## A spike: the generator's reading, checked by the kernel

`spike-tree/` (2026-11-18; `sh spike-tree/red.sh`). For Gauge, and for Climb (a class with a `for`
and a `while`), the meaning of the C++ is said once in Lean (`Cxx.lean`), `tree.py` writes the
tree the generator read each method into (`reader.read`, the tree the model is written from) as
a tree of Cxx.lean's, and the kernel is asked that the tree is the method's words and that its
meaning is the model this generator wrote; for a loop, by induction on its rounds.
Eighteen ways of being wrong are each refused. It is not part of `prove.sh`; `docs/FINDINGS.md`
says what it showed and what it did not.

## What is trusted

Chosen on purpose (SE1/U4), and all of it outside the claims:

- **The compiler and the machine are correct.**
- **The class is called correctly:** a `Bytes` it is given is what it says, that many bytes that
  may be read, fewer than 2^63. That it is used by one thread at a time, and with arguments that
  are apart where one may be written, is no longer only trusted: `lint.py` refuses a program that
  hands what is proved one thing twice where it may write it, as far as that is written at the call, and one that starts a thread beside state
  every thread shares. That a thread is handed only what is its alone, and that a signal handler
  touches nothing proved, are read by a person.
- **Everything outside the class commits no memory error.** `private` is checked by the compiler,
  not by the machine: a stray write elsewhere goes past it. `lint.py` refuses the ways of reaching
  in that are written (an address, a cast, a union), and no others. So the claim holds of a program
  only when every part of it is a domain proved this way, or is listed as assumed.
- **The generator's reading of the C++.** Tested by the comparison (it caught a wrong translation,
  `test_prooc.py`), not proven. Integer conversions are taken from clang's own tree, not worked out
  again. This is the largest thing trusted: all that is owed is derived through it.
- **A `pre( condition )` means at the head of its method's body what it means after its
  parameters.** The generator moves it there to read it. (C++26 evaluates it after the parameters
  are made and before the body; for a constructor, before the fields are, and there a condition
  that names a field is refused.)
- **For a floating type, that a number within finite bounds is finite and is a number.** What is
  proved is `a <= x && x <= b`, with Lean's `Float` for `double`. That no infinity and nothing that
  is not a number satisfies it is IEEE 754's to say; the comparison tries those values, and no
  proof here says it.
- **The invariant says enough.** `return true;` is proved as readily as a real one. But it is in
  the C++, a few lines, read with the class: there is no second text to read.
- **A window is what it says.** `Strong::subarray<const unsigned char*>` (the program's own
  `subarray.h`, read by a person) is read as the byte view. That its elements are there and stay
  is whoever makes one to keep: `lint.py` holds that it is a local or a parameter and that what a
  named one was made from is not changed, and lists each one made by code that is not proved.
  The comparison runs a copy of the class written in `prooc.py`.
- `Prooc.lean` and `Audit.lean`, written by hand, once; Lean's kernel and its library; the three axioms.
- **Lean runs a claims file's commands while it checks it.** `prove.sh` finds a claims file that
  writes over what it is checked against, and no more than that: claims from a stranger are checked
  in a sandbox.

## The subset

Unsigned integers of 8 to 64 bits and `bool`, arrays of them with a fixed size, `static const`
numbers, locals, `if`, `return`, assignment, `+ - * / % & | ^ ~`, shifts, `+= -= *= &= |= ^=`, `++`
and `--` as statements, comparisons, `! && ||` (the right side not read when the left decides),
`while` and `for` with `break` and `continue`, bytes given as a view (below),
calls to the class's own methods written before the caller, `memset( FIELD, BYTE, sizeof( FIELD ) )`
of a whole array of the class, and `throw` (below). One class, one constructor with no arguments, its fields given
values in its initializer list or its body.

**A loop** becomes two functions: one round, and rounds until done, which gives `none` if a stated
number of rounds is not enough; with enough, it is the C++'s run. What is owed says that for some
number there is a result that keeps the invariant: so the C++ ends, and commits no memory error.
How many are enough is a hint in the claims, and nothing owed names it.

**What C++ leaves undefined is `none`**, as a read outside an array is, and "commits no memory
error" in what is owed includes it: a shift by an amount that is not a literal, at the width or
more; a division or remainder by a number that is not a literal, at zero.

**Bytes that are not the class's own come as a view**, read only. Either a `Bytes` parameter, read
by `at()` and `size()`; or, as ordinary C++ has it, a pointer to const bytes with their number, an
unsigned 64-bit parameter, next after it: read by `p[i]`, and the number by its name. What is owed
is that every `i` is below it. A `const char*` (signed bytes) is read through a
`const unsigned char*` local made from it once. A pointer is never moved, compared, kept or handed
on. **Trusted:** that the caller's pointer does point to that many bytes.

**A class proved under another name** (`from/C` with the words `class NAME` after the path): the
class is called NAME where it stands, in its namespaces (gosh: `Strong::Meetup::Header`), and C is
the name it is proved under here (`MeetupHeader`): the Lean names and the files are C's, the C++ the
comparison is compiled with is the class's own. So two parts' classes of one name are two domains.

**A function that is not a method** (`from/C` with the word `function`) is read as a class with no
state and one method, `call`: what is owed of it is that it ends and commits no memory error, for
every argument.

**What a method expects of its caller is said by a type.** A parameter may be a value of another
class read here (`from/C` has a further line, `uses U`). What is owed of the method is then owed
only for values that satisfy `U`'s invariant, which `U`'s own proof shows of every value its
constructor and methods can make. A constructor may take arguments: it is owed to establish the
invariant whatever they are. So nothing is checked when the value is used, and nothing is trusted
of the caller: C++ lets no other value arrive. Such a parameter is used by calling its public
const methods. **Each class is proved apart:** if `U` says too little, `U` is proved and its user's
proof fails; if `U`'s constructor does too little, `U`'s proof fails.

**A part** (since 2026-11-25): a field may be a value of another class read here, which the
class has (`from/C` says `uses U`, as for a parameter). The has-a rule: "the two most important
limitations is not reasoning between several classes. this can be a single class with a has-a
relation to the classes in question" (the owner, 2026-11-24). A part is made by its constructor in
the initializer list, `tray()` or `tray( arguments )`, and must be written there; its public const
methods may be called in expressions and in the invariant, and its other public methods, handed
numbers, as statements of their own. It is never copied, assigned or handed on, so it changes
by its own methods alone. The invariant is then each part's own and, after it, the class's
condition; one that calls a part's method is that the condition has a value and it is true. So
what is owed of the class is owed of every state whose parts keep their own invariants, and
keeping them is owed again here: the claims show it from each part's proof (they may import
`UClaims`, which the audit holds fixed with the class's own files). Each part is still proved
alone: if a part says more than is so, the part is proved and the class that has it is not
(`sample/has/`: a `Station` has-a `Water` and a `Tray`, and keeps the rules that span them: a
shot only where the tank has the water and the tray the room, and the tray holds the drips of the
shots since it was emptied). The comparison's C++ says only the class's own `invariant()`, since a
part's fields are private: the parts' invariants are compared in their own runs.

**A call** to a method of the class is the model of that method. A private method is read and may
be called, and nothing is owed of it alone: it is not on the boundary, and may be called where the
invariant does not hold for a moment. A method that changes the object is called as a statement,
not inside an expression.

**A throw** (`throw E( ... );`, since 2026-11-27) ends the method and tells its caller. Its model
gives back a `Prooc.Thrown`: what it returned, or that it threw; and the state a throw leaves is the
state the method had made by then, so what is owed of it is what is owed of a return: no memory
error, and the invariant kept (C++'s basic guarantee, proved). What is thrown is made of literals
alone and is not read, so it says nothing of the state; that its constructor commits no memory error
is trusted. The comparison catches what the C++ throws and sets it beside the model's.

**An end of the process** (since 2026-11-27): `assert( condition )` where it is not so, and `exit( n )`,
`_exit`, `_Exit` and `abort()`, anywhere in a method's body. Its model gives back that the process
ended, and nothing is owed of the state it leaves, since nothing of the program runs after it; what
follows it may rest on it, as on a `STRONG_CHECK`. Just before an end, a call of the system's whose
arguments are literals (`fprintf( stderr, "..." );`) is passed over: it says why, and reads nothing
of the program's. An assert compiled away (`NDEBUG`) is refused: what follows would rest on a test
not made. The comparison stops where the C++ ends, and both say so (`model/Fuse.hpp`). **Not yet:**
a throw or an end in a constructor or a class template, a call of a method that may throw or end,
and `try`.

**`bool`** is a byte that is 0 or 1. Every way the subset makes one gives one of the two.

**A branch of more than one statement** becomes a function of its own. This is not for the reader's
sake: Lean could not simplify a parser's round as one function (it ran out of time), and could, in
seconds, as five. Each piece gets a lemma, and the pieces are joined.

**What a method expects of its caller** is said by C++26's `pre( condition )`, after its
parameters: a condition on the arguments, and on the fields (not in a constructor, where they have
no values yet). It is never tested when the program runs. The method is owed given it, and its
model is `none` where it is not so: so a caller, whose model calls that model, is proved safe only
if it keeps it. A precondition broken is thus one more thing that cannot happen, like a read
outside an array, and the blame falls on the caller's proof (`sample/stats/grade.h`). A method that
anything outside the proved classes calls is still trusted to be called rightly: what is owed of
it says so, by the `_pre` it is given. A value of another class may be made inside a method, as a
local, `U name( arguments );`, outside any loop, and handed to a method of this class.

The library that reads the C++ does not know `pre`. So the generator reads the text with `pre(...)`
as nothing, finds each condition by its words, and writes it again as the first statement of its
method's body (`gen/C.read.hpp`, kept, and hashed in the bundle); nothing else is changed. The
comparison compiles that text too, with the condition tested, so the script may call anything:
where a condition is false, both sides say `pre` and neither calls.

**A class template, proved once.** `template <typename T, T A, T B> class C` is read as it is
written, not as it is used: its model takes the type and the values, and every statement owed
begins "for every type T whose values compare, and every A and B". Of a T nothing may be done but
to keep it, hand it back, and compare two by `<=`: so the proof cannot rest on what `<=` is, and
holds of an unsigned or a signed integer, a `double` and a `float` alike. `bounded<a, b, type>`
(`trusted/bounded.h`) is the one this was made for: a number from a to b, both included,
whose constructor expects that of its caller. The model is compared with the C++ at four types
(`uint64_t`, `int64_t`, `double`, `float`), a value crossing as its bits, so that the infinities and
what is not a number are tried. A `static_assert` in a class is the compiler's, and is passed over.

A class may take and make a value of such a template at an unsigned type and whole-number bounds
(`sample/strong/tank.h`): it is given the template's invariant at those bounds, and owes the
constructor's precondition where it makes one. The names such a class is written with (a
`typedef`, a `using`, a `static const` number beside the classes) are read from their own files:
`from/C` says `needs FILE NAME` for each.

**Code that is not proved** cannot be shown to keep a precondition, so it may not call anything
that says one. It comes in by what expects nothing: `bounded_checked<a, b, type>` is made from any
number and tests it when the program runs, `STRONG_CHECK( condition, from );`; a method named
`_checked` takes one, makes the bounded number of it, and calls the method that expects that
(`Tank::fill_checked`). **A test that fails ends the process**: it says which line called and what
was expected, and aborts (`trusted/caller.h`). "a failed run-time check is a process kill
with a single caller stack trace (who called this) --- not a catchable exception" (the client,
2026-11-18). So code that is not proved hands over only what it has itself made right. A
`STRONG_CHECK` is read as a `pre` is: the rest of the body may rest on it, since nothing runs
after it otherwise; what differs is that anything may call it. Only a `_checked` constructor or
method may have one, as its first statements.
`ingress.py CLASS...` is the rule: every line under `SUBJECT` that is not one of the proved
classes is code that is not proved, and the program is refused if such a line makes a value whose
constructor says `pre`, or calls a method that does. It is part of proving, as a type error is part
of compiling. It reads words, not meanings (it says how in its head): it can refuse a call that is
another class's method of the same name, and cannot see a value made through a name it was not told.

**What is left to make strong is said.** Each run of `ingress.py` lists every line of code that is
not proved which uses a way in: "the point is to make it strong, and weak code is evident. any
call to _checked better not need it." (the client, 2026-11-18) A test there is a tripwire, not a
gate: it should never fail, and each is a place still to be made strong.

**By a `_checked` name, and by no other.** Code that is not proved calls a proved function or
method only by a name that ends `_checked`, even where nothing can fail: "weak domains can only
call _checked versions, even if those versions cannot fail." (the client, 2026-11-18) A method
that expects nothing and is called only from outside is then simply named so. `ingress.py` refuses
any other call, and its list of the ways in used is every place the two kinds of code meet.

**Where what is proved stands.** With `STRONG=dir`, `ingress.py` also holds that what is proved is
under that directory and in the namespace of its name (`strong/`, `Strong`), and that nothing else
with a body is: so where a line stands says whether it is proved. And the generator refuses a
proved method, other than one named `..._checked`, that takes, makes or calls anything `_checked`:
what is proved is called by what is proved, and tests nothing when the program runs.
`sample/strong/` is such a directory; `sample/weak/outside.h` is code that is not proved.

**What a proof takes as given of the program around it is looked for.** A class is proved alone,
one method at a time. That is all that is owed only if the rest of the program lets it be, and no
proof of the class can say so. `lint.py` (with `SUBJECT`, `STRONG`, and `INCLUDE` for where else
the program's `#include`s are) reads every file as Clang does, and refuses the program unless:
- **one name:** at a call of anything of the program's own, proved or not, what the call may write
  by reference or by pointer (or the object of a method that is not const) is not one thing with
  another argument or the object, or a part of it: non-const aliases are unique, and arguments
  that are only read may be one thing. At a call of what is proved, an argument that is not a name,
  beside anything the call may write, is refused: the caller hands a name, a copy where it may be
  the same (at a call of the system's such a pair is said, not refused);
- **one owner:** nothing that can be written is shared by every object and thread (a global, a
  static) under `STRONG`; elsewhere each is said, and a thread may be started only where there is
  none; a signal handler that is a function is said, each one;
- **own bytes:** outside `STRONG` a proved value's address is not taken, a pointer or reference to
  it is not cast, and it is not in a union: its fields are changed by its methods and nothing else;
- **a window:** a `subarray` is a local or a parameter, what a named one was made from is not
  changed while it is in scope, and outside `STRONG` nothing of one is called;
- **nothing leaves:** no public method of a class under `STRONG` gives back a pointer, a
  reference, a view or an iterator to its own object's state (of any other class it is said);
- **a context:** what a function recalls (`retain.hpp`) it needs retained, and so does whatever
  calls it, up to one that retains it first; `main` may not need one, and a function nothing of
  the program calls that does is said. A retain is a local, what is recalled is not kept or
  pointed elsewhere, and nothing under `STRONG` retains or recalls.

"the lint step is part of a full compile: c++ compile, lint, prove. ... in the end proofs should
only need to work out the correctness of a domain." (the client, 2026-11-19) So the order is the
compiler, then the generator's reading (`READ_ONLY=1 prove.sh`, which writes `gen/`), `ingress.py`
and `lint.py`, then the proofs. It reads what is written at the call: it does not see one thing
reached by two names, an argument that is not a name where nothing is written, bytes written over a
struct that has a proved value in it, or a reference into a container that then grows. A file it
cannot read whole is refused.

**A window.** A parameter of type `Strong::subarray<const unsigned char*>` is a byte view, read
by `at( i )` and `size()`: what is owed is that every index is below `size()`, as for a pointer
and its length. No sample here has one yet: it is exercised by the program this was built for,
and by `lint.py`'s cases. A `Strong::fixed<N, of>` (the same `subarray.h`) is a window of N bytes by
its type: it is read only at an index written out below N, and any other index is refused, so its
reads cannot fail and nothing is owed of them; its `size()` is N. Whoever makes one keeps that the
N bytes are there (gosh: `src/meetup/sealed.h`, where the length has just been found N).

**Not yet:** a class that uses a template at a signed or a floating type (the template is proved of
those; the classes that use it are read with unsigned numbers only); arithmetic on a T;
a precondition that reads an array or calls a method; one of a function or method that
a class other than its own calls (but for a constructor); a part of a class template, or in one,
and a part handed to a method or one of its methods handed a part or a view,
calls to a function, a reference parameter (so a function cannot
give back more than one number), a local array, bases and `virtual`, `switch`, `std::string`. A
class named as something of Lean's own (`Sum`, `List`) does not compile there, and fails loudly.

## What is claimed, written as a test that cannot be run

What is proved of a class was said only in `gen/COwed.lean`, which a person must read in Lean. "it
shoud look like C++ code but would be impossible to actually run ... this is how invariants should
be shown as auditable by humans"; "the goal is an auditable proof by a regular programmer" (the
client, 2026-11-19). So `proofs/Gauge.proof.cpp` says what is claimed of `Gauge` as the test one
would write if a machine could run it:

    PROOF( a_gauge_is_never_above_its_limit )
    {
      Gauge gauge;
      for ( uint32_t limit : all<uint32_t>() ) {
        gauge.setLimit( limit );
        PROVE( gauge.getLimit() == limit );

        for ( uint32_t value : all<uint32_t>() ) {
          gauge.set( value );
          PROVE( gauge.get() <= limit );
          PROVE( gauge.get() == ( value <= limit ? value : limit ) );
          PROVE( gauge.getLimit() == limit ); /* (the next round rests on it) */

`model/forall.h` makes that C++: `all<T>()` does step through every value of `T`, so the compiler
checks every name and type against the class; run, the two loops are 2^64 rounds. `prove.sh`
compiles it, `proofs.py` makes of it what is owed (`gen/GaugeProofOwed.lean`), and
`claims/GaugeProofClaims.lean` proves that, audited as any claims are. **To know what is proved of
Gauge, a programmer reads the proof file, and no Lean.**

How a loop is read, which is the one thing to know. A loop over every value cannot be followed
round by round, so each loop is one statement: from any state the rounds before could leave,
every `PROVE` in a round holds, and the round leaves such a state. What a round knows of the
rounds before is the class's invariant, and what the loop's last `PROVE`s say without naming the
loop's own variable. So what a later round rests on is written as a `PROVE` at the end of the
loop (the last line above); take it away, and the loop is not proved (`test_prooc.py` does).

**What is trusted for this, besides what is trusted above:** that `proofs.py` reads the test
rightly. It is 300 lines, reads a small subset and refuses the rest. Nothing can run a proof file
whole, but it can be run small (since 2026-11-21): compiled with `PROOC_RUN`, `model/forall.h` takes
each loop over whole numbers at its first and last 8 values, and each over bytes at a fixed seeded
sample, and a false `PROVE` says which and where. `prove.sh` runs it so, with the byte view checked
and under the sanitizers, after `proofs.py` has read the file (what it does not know is refused, not
run) and before Lean: a claim that is false when run is not proved, and fails in a second. That sets the reading against a run; it does not prove the reading.

A class read from another program has its proof file in that domain (`proofs/C.proof.cpp`, which
includes the program's own header). And a loop may be over every sequence of bytes there is,
`for ( const std::vector<unsigned char>& b : every_bytes() )`, handed on as a window
(`W( b.data(), b.size() )`): that is what a fuzzer samples, said of all of it. Or over every
sequence of n bytes, `every_bytes( n )`, the only thing a fixed window of n is made of in a proof
file (`W( b.data() )`); each round may rest on the length.

A method may be handed what a const method of the same object gives (`gauge.set( gauge.get() )`),
and a loop inside another knows the bounds of the one around it (both since 2026-11-19: the
second had been left out, which made a statement ask more than the file said, never less).

**A proof of a set** (since 2026-11-22). A domain is a set of classes and functions, the simplest
one of either: "make the prover bend, not the world" (the owner). So a proof file is of the class
whose file it is and of every domain proved before it in the run: it may make objects of any of
their classes, each once, and call their functions (`sample/set/`: `proofs/Jar.proof.cpp` makes two
jars and calls `fits`). Each class and function is still proved alone; the proof file is where
what they do together is claimed. A function is called in a condition or to make what a method is
handed, not as a statement, since what it gives would be kept nowhere.

**Not yet:** arithmetic in a condition; a method's result kept
in a variable; a class with floats
(`sample/bottle/bottle.proof.cpp` is such a file, compiled and not proved: queue item 20).

## Another program's classes, read where they stand

A model written again by hand from another program's code is one more text to audit, every time
that code changes. So the generator reads the class where it is:

```sh
echo stats/histogram.h > from/Histogram                    # the file, under SUBJECT
SUBJECT=prover/sample ./prover/prove.sh Histogram
```

It finds `class Histogram` in that file, and takes its text, not one character changed, with
`<cstdint>` and `<cstring>` before it and its namespaces around it (`gen/Histogram.subject.hpp`).
The file need not compile alone, and what else is in it is not read. The class's text must compile
alone, with no error. Everything owed is derived from that text, the comparison runs that text, and
the bundle names the file, its hash and the commit it was read at.

Such a class may say no invariant (`--invariant-may-be-absent`): it cannot be changed from here.
Then nothing is claimed of its state, what is owed is memory and ending alone, and `prove.sh` says so.

**Trusted here, and not shown:** that the class means alone what it means in its file. A macro
defined by another header, or a name the class takes from one, could change that; a name it needs
and does not have fails to compile, and is refused.

`DOMAIN=/path/to/dir prove.sh C` proves classes listed in another project: `dir/from/C` or
`dir/model/C.hpp`, with `dir/claims/CClaims.lean` (and `dir/scripts/C.py`), and `gen/` and `build/`
written there.

The spike's real case is kept that way, outside this repository, because it is written from
another project's code: a parser of STUN answers, bytes from anyone on the Internet. Proved of it,
for every sequence of bytes of any length: `parse` ends; it reads nothing outside the bytes and
writes nothing outside its 16; what it keeps is nothing, IPv4 or IPv6; and an IPv6 address it keeps
is never of one link alone (`fe80::/10`). 144 lines of C++, 388 of proof, checked in 9 seconds.
What that found is in `docs/FINDINGS.md`.
