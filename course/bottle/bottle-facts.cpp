/* Lesson 1: the bottle, tested. Each FACT is one case someone thought of.
   Build and run:  c++ -std=c++17 -I../../vendor/facts bottle-facts.cpp ../../vendor/facts/facts.cpp -o bottle-facts && ./bottle-facts */
#include <cstdint>

#include "Bottle.hpp"
#include "facts.h"

FACTS( ANewBottle )
{
  Bottle bottle;
  FACT( bottle.getVolume() == 0u );
  FACT( bottle.getMaxVolume() == 1u );
}

FACTS( PouringIn )
{
  Bottle bottle;
  bottle.setMaxVolume( 750 );
  bottle.setVolume( 500 );
  FACT( bottle.getVolume() == 500u );  /* what fits stays */
  bottle.setVolume( 1000 );
  FACT( bottle.getVolume() == 750u );  /* what does not, spills */
  bottle.setVolume( 0 );
  FACT( bottle.getVolume() == 0u );    /* and it can be emptied */
}

FACTS( ASmallerBottle )
{
  Bottle bottle;
  bottle.setMaxVolume( 750 );
  bottle.setVolume( 750 );
  bottle.setMaxVolume( 330 );
  FACT( bottle.getVolume() == 330u );  /* what no longer fits spills out */
}

/* Lesson 2: what is always true, checked after every call, over many calls. Still only the
   calls made here: a few thousand of the 2^64 pairs there are. */
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

FACTS_REGISTER_ALL()
{
  FACTS_REGISTER( ANewBottle );
  FACTS_REGISTER( PouringIn );
  FACTS_REGISTER( ASmallerBottle );
  FACTS_REGISTER( AlwaysNoMoreThanItHolds );
}

FACTS_MAIN
