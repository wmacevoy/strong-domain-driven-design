/*
  What is claimed of Gauge (model/Gauge.hpp), as a test that cannot be run: model/forall.h says
  how it is read. The prover makes of it the statements in gen/GaugeProofOwed.lean, and
  claims/GaugeProofClaims.lean proves them. So to know what is proved of Gauge, read this.
*/
#include <cstdint>

#include "Gauge.hpp"
#include "forall.h"

/* Whatever limit it is given, and then whatever level, the level is never above the limit:
   what is set is what is there if it fits, and the limit if it does not. */
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
      PROVE( gauge.getLimit() == limit ); /* (setting the level leaves the limit: the next round rests on it) */
    }
  }
}

/* Lowering the limit lowers a level that was above it, and leaves one that was not. */
PROOF( lowering_the_limit_brings_the_level_down_with_it )
{
  for ( uint32_t limit : all<uint32_t>() ) {
    for ( uint32_t value : all<uint32_t>() ) {
      for ( uint32_t lower : all<uint32_t>() ) {
        Gauge gauge;
        gauge.setLimit( limit );
        gauge.set( value );
        gauge.setLimit( lower );
        PROVE( gauge.getLimit() == lower );
        PROVE( gauge.get() <= lower );
        PROVE( gauge.get() == ( value <= limit ? ( value <= lower ? value : lower ) : ( limit <= lower ? limit : lower ) ) );
      }
    }
  }
}
