# Lesson 1. Facts: the bottle, tested

A bottle holds some volume, from nothing up to its size. Pour in more than fits, and the rest
spills. Swap it for a smaller bottle, and what no longer fits spills too.

```cpp
class Bottle
{
public:
  Bottle() { volume = 0; maxVolume = 1; }

  uint32_t getVolume() const { return volume; }
  uint32_t getMaxVolume() const { return maxVolume; }

  void setVolume( uint32_t value )
  {
    if ( value > maxVolume ) { value = maxVolume; }
    volume = value;
  }

  void setMaxVolume( uint32_t value )
  {
    maxVolume = value;
    if ( volume > maxVolume ) { volume = maxVolume; }
  }

private:
  uint32_t volume;
  uint32_t maxVolume;
};
```

(The whole file, with comments, is `bottle/Bottle.hpp`. The numbers are unsigned whole numbers on
purpose: lesson 4 says why.)

## A fact is one case

The usual way to gain confidence in this class is to write tests. Here they are written with
*facts*, a small C++ test library (`vendor/facts`): `FACT( a == b )` checks a comparison, and when
it is false prints both sides.

```cpp
FACTS( PouringIn )
{
  Bottle bottle;
  bottle.setMaxVolume( 750 );
  bottle.setVolume( 500 );
  FACT( bottle.getVolume() == 500u );  /* what fits stays */
  bottle.setVolume( 1000 );
  FACT( bottle.getVolume() == 750u );  /* what does not, spills */
}
```

Build and run them (`bottle/bottle-facts.cpp` has four groups):

```sh
c++ -std=c++17 -Ivendor/facts course/bottle/bottle-facts.cpp vendor/facts/facts.cpp -o build/bottle-facts
build/bottle-facts
```

```
10006 (100.0%) truths and 0 (0.0%) fictions checked.
```

Each fact is evidence about **one case**: a bottle of 750 holding 500. Four groups of facts say
four kinds of case work. They say nothing about a bottle of 4,294,967,295, or about pouring 751
into a bottle of 750, unless someone wrote that case.

## A bug the facts miss

Change one line of `setMaxVolume`, as a tired programmer might:

```cpp
    if ( volume > maxVolume + 1 ) { volume = maxVolume; }   /* was: volume > maxVolume */
```

Now a bottle holding exactly one more than its new size keeps it. Run the facts again: **all
10,006 still pass.** None of them made a bottle hold exactly one more than its new size. (The
random ones in lesson 2 do not either: the chance of hitting it is tiny.)

This is not a bad test suite. It is what tests are: the cases you thought of. The rest of this
course is about saying something of **every** case, and having a machine check it.

> Seen 2026-11-21: with that change, the facts pass and the proof of lesson 5 fails.

## Exercises

1. Write a fact that catches the off-by-one above. What did you have to think of first?
2. How many different calls `setVolume( x )` are there? How many pairs of calls
   `setMaxVolume( m ); setVolume( x );`? At a billion facts a second, how long to run them all?
3. Write down, in one English sentence, what is true of every bottle after any calls at all.
   Lesson 2 starts from that sentence.
