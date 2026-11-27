/*
  prover sample: a call of a function outside the program, by its contract. take_in is the
  program's own, or a library's: it is not read. from/Gather says what it may do: it writes at most
  n bytes at out, and gives back how many it wrote, or -1. What is owed of Gather is then owed for
  every answer take_in could give that keeps its contract; that it keeps it is what is trusted.
*/
#include <cstdint>

/* Fills at most n bytes at out; says how many, or -1 if it could not. Not read: its contract is in from/Gather. */
int take_in( unsigned char* out, uint64_t n );

namespace Outside {

class Gather
{
private:
  unsigned char room[32];
  uint64_t got;

public:
  Gather() : room(), got( 0 ) {}

  /* Takes in what there is, into its room; false if nothing could be. */
  bool gather( void )
  {
    int n = take_in( room, 32 );
    if ( n < 0 ) {
      return false;
    }
    got = (uint64_t)n;
    return true;
  }

  uint64_t size( void ) const { return got; }

  bool invariant() const { return got <= 32; }
};

}
