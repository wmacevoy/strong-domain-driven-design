# Lesson 3. A test that cannot be run

What you mean when you say "the bottle is correct" is a test with no missing cases: for every
size, and every volume poured in, the volume is never more than the size. Write that test:

```cpp
PROOF( a_bottle_never_holds_more_than_its_size )
{
  Bottle bottle;
  for ( uint32_t size : all<uint32_t>() ) {
    bottle.setMaxVolume( size );
    PROVE( bottle.getMaxVolume() == size );

    for ( uint32_t value : all<uint32_t>() ) {
      bottle.setVolume( value );
      PROVE( bottle.getVolume() <= size );
      PROVE( bottle.getVolume() == ( value <= size ? value : size ) );
      PROVE( bottle.getMaxVolume() == size ); /* (pouring leaves the size: the next round rests on it) */
    }
  }
}
```

(`bottle/Bottle.proof.cpp`.) It reads like lesson 1's facts. It **is** C++: `PROOF`, `PROVE` and
`all<T>()` come from `prover/model/forall.h`, and `all<uint32_t>()` really does step through every
32-bit number. The compiler checks every name and type against the class:

```sh
c++ -std=c++17 -fsyntax-only -Iprover/model -Icourse/bottle course/bottle/Bottle.proof.cpp
```

Run it, and the two loops are 2^32 × 2^32 = 2^64 rounds: at a billion a second, about 585 years.
Nobody runs it. It is not there to be run. It is there to be **read** (by you, by a reviewer, by
your future self) and to be **proved** (by the prover, lesson 5).

## Reading a loop over every value

A loop that cannot be run cannot be followed round by round. So each loop is read as one
statement about all of its rounds at once:

> From any state the rounds before could leave, every `PROVE` in this round holds, and the round
> leaves such a state again.

"Any state the rounds before could leave" is everything the prover knows going into a round:

- the class's invariant (`volume <= maxVolume`), which every method keeps (lesson 2), and
- what the loop's last `PROVE`s say, if they do not name the loop's own variable.

That second point is the one thing to learn here. Look at the last `PROVE` of the inner loop:

```cpp
      PROVE( bottle.getMaxVolume() == size ); /* (pouring leaves the size: the next round rests on it) */
```

It looks redundant: of course pouring does not change the size. But the *next* round's
`PROVE( bottle.getVolume() <= size )` needs to know the size is still `size`, and the only things
a round knows about the rounds before it are the invariant and those last `PROVE`s. Take that
line out, and the inner loop's statement is false (some earlier round *could*, as far as the
statement knows, have changed the size), and the proof fails. As it should.

That is induction again: the last `PROVE`s are the **loop invariant**, the thing carried from
round to round. Here you write it in C++, as one more line of the test.

## Exercises

1. Write a `PROOF` that a bottle can always be emptied: for every size and every volume,
   `setVolume( 0 )` leaves `getVolume() == 0`. Does it need a carried `PROVE`? Why not?
2. `bottle/Bottle.proof.cpp` has a second proof, about a smaller bottle, with three nested loops
   and a new bottle each round. Why does it need no carried `PROVE`?
3. In the first proof, what would go wrong if `Bottle bottle;` were inside the outer loop instead
   of before it? (Nothing! Explain why, then say what changes in what each round knows.)
