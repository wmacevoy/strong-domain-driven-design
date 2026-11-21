# Lesson 2. What is always true

The sentence from lesson 1's last exercise is probably something like: *there is never more in
the bottle than it holds.* That is an **invariant**: true of every bottle, after any calls, in any
order, with any numbers.

Write it as code, in the class, where it cannot drift from the code it describes:

```cpp
  /* There is never more in it than it holds. (Never less than nothing: it is unsigned.) */
  bool invariant() const { return volume <= maxVolume; }
```

An invariant written in a comment, or in a document, is a wish. Written as a method, it can be
checked by a test, and (lesson 5) proved.

## Three things an invariant must be

- **True of a new object.** The constructor makes it so: `volume = 0; maxVolume = 1;`, and
  0 ≤ 1.
- **Kept by every method.** If it is true before a call, it is true after. `setVolume` clamps the
  value to `maxVolume`; `setMaxVolume` spills what no longer fits. Each, alone, keeps it.
- **About the object's own state.** It reads only the fields. Nothing outside can change them
  (they are `private`), so nothing outside can break it.

If those three hold, the invariant holds forever: it starts true, and no call can make it false.
That argument is **induction** on the number of calls, and it is the whole idea of this course in
one paragraph. Lesson 3 writes it as a loop; lesson 5 has a machine check it.

## Checking it after every call

A test can check the invariant after every call, over many calls (`bottle/bottle-facts.cpp`):

```cpp
FACTS( AlwaysNoMoreThanItHolds )
{
  Bottle bottle;
  uint32_t seed = 20261121; /* seeded: the same calls every run */
  for ( int round = 0; round < 10000; round++ ) {
    seed = seed * 1664525u + 1013904223u;
    if ( seed & 1 ) {
      bottle.setMaxVolume( seed >> 20 );
    } else {
      bottle.setVolume( seed >> 19 );
    }
    FACT( bottle.invariant(), "round " << round );
  }
}
```

This is better than lesson 1's facts in one way: it states the *rule* rather than one answer, so
any case it reaches is checked against it. It is no better in another: it reaches ten thousand
cases out of an endless number. With lesson 1's off-by-one in place, it still passes.

(Why seeded? A test that picks different numbers each run can pass today and fail tomorrow with
no change to the code, and then nobody trusts it. Seed it, and a failure happens again when you
look.)

## Exercises

1. Write an invariant that is too weak: always true, and useless. (Hint: `return true;`.) What
   would a proof of it tell you?
2. Write one that is too strong: false of some bottle the class can really make. Which method
   breaks it?
3. Explain, in your own words, why "true of a new object" and "kept by every method" together
   mean "true after any calls". Where does `private` come in?
