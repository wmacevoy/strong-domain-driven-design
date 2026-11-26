# trusted

What a program's proofs rest on, owned here and nowhere else. A program that is proved by this
prover keeps an exact copy of each file it uses, under its own `src/strong/`: it must build without
this project, and the copy is checked, byte for byte, against this one at the prover's commit it is
proved with (gosh: `tools/proofs.sh`, at `tools/prover.commit`). The names were chosen by the owner,
2026-11-26: "call it trusted".

| File | What it is | Held by |
| --- | --- | --- |
| `bounded.h` | `bounded<a, b, type>`: a number from a to b as a type, made by a proved class, which owes the bounds; `bounded_checked<a, b, type>`: the same, made by anyone, tested when it is made | **proved** here, once for every type and bounds: `from/bounded_of`, `from/bounded_checked_of`, `claims/`, and the red cases in `test_prooc.py`. A class that takes one rests on that proof (gosh's `CounterWindow`) |
| `caller.h` | who called a way in, and the end of the process when what it tests is not so | read by a person: it writes to standard error and ends the process |
| `subarray.h` | a window on elements one after another (`subarray`), and one whose length is its type (`fixed`) | read by a person, and by the lint: each keeps a pointer, which no proved class may |

The samples use them where they stand (`sample/strong/bounded.h` and `caller.h` are links here).
A change to one is a change to every program that copies it: it is proved here first, and a program
takes it by moving its prover commit and its copy together.
