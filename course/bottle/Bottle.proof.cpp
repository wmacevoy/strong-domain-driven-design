/*
  Lesson 3: what is claimed of Bottle, as a test that cannot be run. It looks like
  bottle-facts.cpp, and it is C++ the compiler checks; but each loop is over every value there
  is (all<uint32_t>(): 2^32 of them), so the two together are 2^64 rounds. Nobody runs it. The
  prover reads it as a statement about every round, and Lean checks a proof of that statement
  (Bottle.proof-claims.lean, lesson 5). To know what is proved of Bottle, read this file.
*/
#include <cstdint>

#include "Bottle.hpp"
#include "forall.h"

/* Whatever size it is made, and then whatever is poured in, there is never more in it than it
   holds: what is poured is what is there if it fits, and the size if it does not. */
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

/* A smaller bottle spills what no longer fits, and keeps what does. */
PROOF( a_smaller_bottle_spills_what_no_longer_fits )
{
  for ( uint32_t size : all<uint32_t>() ) {
    for ( uint32_t value : all<uint32_t>() ) {
      for ( uint32_t smaller : all<uint32_t>() ) {
        Bottle bottle;
        bottle.setMaxVolume( size );
        bottle.setVolume( value );
        bottle.setMaxVolume( smaller );
        PROVE( bottle.getVolume() <= smaller );
        PROVE( bottle.getVolume() == ( value <= size ? ( value <= smaller ? value : smaller ) : ( size <= smaller ? size : smaller ) ) );
      }
    }
  }
}
