/*
  prover model: a method that ends the process. Ordinary C++; nothing here knows the tool.
  After an end nothing of the program runs, so nothing is owed of the state it leaves: only that
  there is no memory error on the way to it. blow() ends the process at the fourth blow, saying why
  first; until then it keeps the count at most 3.
*/
#pragma once
#include <cstdint>
#include <cstdio>
#include <cstdlib>

class Fuse {
public:
  Fuse() : blows( 0 ) {}

  /* One more blow; the fourth ends the process. */
  uint32_t blow()
  {
    if ( blows == 3 ) {
      fprintf( stderr, "the fuse is blown\n" );
      exit( 1 );
    }
    blows = blows + 1;
    return blows;
  }

  uint32_t count() const { return blows; }

  bool invariant() const { return blows <= 3; }

private:
  uint32_t blows;
};
