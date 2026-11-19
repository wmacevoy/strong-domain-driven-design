/*
  prover sample: bytes given as a pointer and a length, the way ordinary C++ gives them.

  frame_begins is a function that is not a method, over `const char*`, whose bytes are signed: it
  reads them through a `const unsigned char*` made from it, as such code does.  Checksum is a class
  whose method takes `const unsigned char*` and reads it directly.  In both, the parameter after
  the pointer is its length, and what is owed is that no byte at or past it is read.
*/
#include "wire/not-here.h"
#include <cstddef>
#include <cstdint>

namespace Wire {

/* True if these bytes begin a frame: its mark, a version of 2 or less, and a body that fits. */
inline bool frame_begins( const char* data, size_t n )
{
  const unsigned char* p = reinterpret_cast<const unsigned char*>( data );
  if ( n < 4 || p[0] != 0xF7 || p[1] > 2 ) {
    return false;
  }
  const size_t body = ( static_cast<size_t>( p[2] ) << 8 ) | p[3];
  return body <= n - 4;
}

class Checksum
{
private:
  uint32_t sum;
  uint64_t bytes;

public:
  Checksum() : sum( 0 ), bytes( 0 ) {}

  void add( const unsigned char* data, size_t len )
  {
    for ( size_t i = 0; i < len; i++ ) {
      sum += data[i];
    }
    bytes += len;
  }

  uint32_t get( void ) const { return sum; }

  bool invariant() const { return true; }
};

}
