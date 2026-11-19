/*
  prover sample: a file of "another program", to read a class from as it stands.

  This file does not compile alone (its first include is of nothing), and it has a second class
  and a global beside the one that is read: the generator takes the text of class Histogram and
  nothing else.  Histogram is written the way ordinary C++ is, not the way the first models were:
  an initializer list, a constant, private methods that the public ones call, bool, %, /, +=, ++
  and a memset of a whole array.
*/
#include "stats/not-here.h"
#include <cstdint>
#include <cstring>

namespace Stats {

int beside = 0;

class Other {
public:
  int anything;
};

class Histogram
{
public:
  static const uint32_t BINS = 8;

private:
  uint32_t count[BINS];
  uint32_t total;
  bool wrapped;

  bool full( uint32_t bin ) const { return count[bin % BINS] == 0xffffffff; }
  void bump( uint32_t bin )
  {
    count[bin % BINS] += 1;
    total++;
  }

public:
  Histogram() : count(), total( 0 ), wrapped( false ) {}

  /* One more of this value: false, and nothing counted, if its bin can hold no more. */
  bool add( uint32_t value )
  {
    if ( full( value ) ) {
      wrapped = true;
      return false;
    }
    bump( value );
    return true;
  }

  /* The share of a bin in parts of `parts`; 0 if nothing is counted. */
  uint32_t share( uint32_t bin, uint32_t parts ) const
  {
    if ( total == 0 || bin >= BINS ) {
      return 0;
    }
    return count[bin] * parts / total;
  }

  uint32_t largest( void ) const
  {
    uint32_t most = 0;
    for ( uint32_t i = 0; i < BINS; i++ ) {
      if ( count[i] > most ) {
        most = count[i];
      }
    }
    return most;
  }

  void reset( void )
  {
    memset( count, 0, sizeof( count ) );
    total = 0;
    wrapped = false;
  }

  bool invariant() const { return total == count[0] + count[1] + count[2] + count[3] + count[4] + count[5] + count[6] + count[7]; }
};

}
