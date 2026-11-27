/*
  prover sample: bytes a class owns in a buffer of the program's own type, made of a number of
  bytes its constructor gives. The prover does not read the buffer's type (it holds a pointer, and
  calls the allocator): the program says it is one (from/Holder: `buffer Block data len`), and a
  person reads that it is: made of its length, which it keeps, data() where its bytes are and len()
  their number. Holder is then read as if the buffer were an array of that many bytes.
*/
#include <cstdint>
#include <cstdlib>
#include <cstring>

namespace Held {

/* A buffer of bytes the program owns: made of its length, which it keeps. Not proved: read by a person. */
class Block
{
private:
  size_t n;
  unsigned char* p;

public:
  explicit Block( size_t len ) : n( len ), p( static_cast<unsigned char*>( calloc( len, 1 ) ) ) {}
  ~Block() { free( p ); }
  unsigned char* data( void ) const { return p; }
  size_t len( void ) const { return n; }
  Block( const Block& ) = delete;
  Block& operator=( const Block& ) = delete;
};

class Holder
{
public:
  static const uint64_t ROOM = 64;

private:
  Block held;
  uint64_t kept;

public:
  Holder() : held( ROOM ), kept( 0 ) {}

  /* Holds the n bytes at p, if there is room; false if not. */
  bool hold( const unsigned char* p, uint64_t n )
  {
    if ( n > held.len() ) {
      return false;
    }
    memcpy( held.data(), p, n );
    kept = n;
    return true;
  }

  uint64_t size( void ) const { return kept; }

  bool invariant() const { return kept <= ROOM; }
};

}
