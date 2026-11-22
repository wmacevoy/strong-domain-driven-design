/*
  What is claimed of the set {Jar, fits}, as a test that cannot be run: two objects, and a
  function called in a condition and as an argument. Lean checks a proof of it
  (claims/JarProofClaims.lean).
*/
#include <cstdint>

#include "set/fits.h"
#include "set/jar.h"

#include "forall.h"

/* Into two new jars, n beans, and what fits of n: the two hold the same; and what a jar holds
   fits in it. */
PROOF( what_fits_is_what_a_jar_takes )
{
  for ( uint32_t n : all<uint32_t>() ) {
    Jar a;
    Jar b;
    a.add( n );
    b.add( fits( n, 100 ) );
    PROVE( a.count() == b.count() );
    PROVE( fits( a.count(), 100 ) == a.count() );
  }
}
