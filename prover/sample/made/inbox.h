/*
  prover sample: a view whose length is a bounded number (bounded.h).

  Inbox::keep is handed bytes and their number as a Length, a number from 0 to 64: it copies them
  into its 64 places with no test. That they fit is had from the type, which was proved once, of
  every type and every pair of bounds; whoever makes a Length owes that it is within them, and is
  given that the view has that many bytes. Ordinary C++; nothing here knows the tool.
*/
#include "strong/bounded.h"
#include <cstdint>
#include <cstring>

namespace Strong {

typedef bounded<0, 64, uint64_t> Length;

class Inbox
{
private:
  unsigned char held[64];
  uint64_t count;

public:
  Inbox() : held(), count( 0 ) {}

  /* Keeps the n bytes of p. */
  void keep( const unsigned char* p, Length n )
  {
    memcpy( held, p, n.number() );
    count = n.number();
  }

  /* Byte i of what is kept, or 0 past it. */
  uint32_t at( uint64_t i ) const
  {
    if ( i >= count ) {
      return 0;
    }
    return held[i];
  }

  bool invariant() const { return count <= 64; }
};

}
