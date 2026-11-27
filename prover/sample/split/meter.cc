/* prover sample: the definitions of meter.h's methods. */
#include "split/meter.h"

using namespace Split;

Meter::Meter() : reading( 0 ), most( 1000 ) {}

uint32_t Meter::add( uint32_t n )
{
  if ( n > most - reading ) {
    reading = most;
  } else {
    reading = reading + n;
  }
  return reading;
}

uint32_t Meter::value( void ) const
{
  return reading;
}
