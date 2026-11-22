/*
  What is claimed of fits, as a test that cannot be run: a function's own proof file calls it.
  Lean checks a proof of it (claims/fitsProofClaims.lean).
*/
#include <cstdint>

#include "set/fits.h"

#include "forall.h"

/* What fits is never more than the room, nor more than there is. */
PROOF( what_fits_is_at_most_the_room_and_what_there_is )
{
  for ( uint32_t n : all<uint32_t>() ) {
    for ( uint32_t room : all<uint32_t>() ) {
      PROVE( fits( n, room ) <= room && fits( n, room ) <= n );
    }
  }
}
