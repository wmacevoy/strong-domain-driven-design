/*
  The same, of Gauge (model/Gauge.hpp): the bottle with whole numbers, which the prover does read
  and has proved (claims/GaugeClaims.lean). NOT YET READ BY THE PROVER in this form: what is
  proved of Gauge today is what gen/GaugeOwed.lean says, which a person reads in Lean. This file
  says the same to a person who reads C++.
*/
#include <cstdint>

#include "../../model/Gauge.hpp"
#include "forall.h"

PROOF( a_gauge_is_never_above_its_limit )
{
  Gauge gauge;
  for ( uint32_t limit : all<uint32_t>( 0, UINT32_MAX ) ) {
    gauge.setLimit( limit );
    PROVE( gauge.invariant() && gauge.getLimit() == limit );

    for ( uint32_t value : all<uint32_t>( 0, UINT32_MAX ) ) {
      gauge.set( value );
      PROVE( gauge.get() <= limit );
      PROVE( gauge.get() == ( value <= limit ? value : limit ) );
    }
  }
}
