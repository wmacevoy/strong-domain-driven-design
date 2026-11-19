/*
  What is claimed of Bottle, as a test that cannot be run (forall.h says how it is read).
  NOT YET PROVED: the prover does not read this file, nor a class with floats in it. Today it is
  compiled, and no more: its names and types are right, and what it claims is here to be read.
*/
#include <cfloat>

#include "bottle.h"
#include "../../model/forall.h"

PROOF( a_bottle_holds_from_nothing_up_to_its_size )
{
  for ( float max_volume : all<float>( 0, FLT_MAX ) ) {
    Bottle bottle( max_volume );
    PROVE( bottle.invariant() );
    PROVE( bottle.getVolume() == 0 && bottle.getMaxVolume() == max_volume );

    for ( float value : all<float>( 0, FLT_MAX ) ) {
      bottle.setVolume( value );
      PROVE( bottle.invariant() );
      PROVE( 0 <= bottle.getVolume() && bottle.getVolume() <= max_volume );
      /* what is put in is what is there, if it fits; and the bottle is full, if it does not */
      PROVE( bottle.getVolume() == ( value <= max_volume ? value : max_volume ) );
    }
  }
}

/* And a bottle can be emptied, from however full. */
PROOF( a_bottle_can_be_emptied )
{
  for ( float max_volume : all<float>( 0, FLT_MAX ) ) {
    for ( float value : all<float>( 0, FLT_MAX ) ) {
      Bottle bottle( max_volume );
      bottle.setVolume( value );
      bottle.setVolume( 0 );
      PROVE( bottle.getVolume() == 0 );
    }
  }
}
