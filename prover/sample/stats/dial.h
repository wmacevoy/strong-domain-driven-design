/*
  prover sample: what a method expects of its caller, said by a type.

  Percent is a number from 0 to 100.  Its constructor makes any number into one (it takes the
  remainder by 101), so its invariant is true however it is made, and nothing is checked when it
  is used.  Dial::mark takes a Percent and indexes an array of 101 by it, with no test: that it
  stays inside the array is proved from Percent's invariant, not from anything in Dial.

  So "mark is called with a number below 101" is not something a caller is trusted for.  C++
  itself lets no other number arrive: a Percent is the only thing mark takes, and Percent's
  constructor is the only way to make one.
*/
#include "stats/not-here.h"
#include <cstdint>

namespace Stats {

class Percent
{
public:
  static const uint32_t MOST = 100;

private:
  uint32_t value;

public:
  explicit Percent( uint32_t raw ) : value( raw % 101 ) {}

  uint32_t number( void ) const { return value; }

  bool invariant() const { return value <= MOST; }
};

class Dial
{
private:
  uint32_t seen[101];
  uint32_t last;

public:
  Dial() : seen(), last( 0 ) {}

  void mark( Percent p )
  {
    seen[p.number()] += 1;
    last = p.number();
  }

  uint32_t times( Percent p ) const { return seen[p.number()]; }

  bool invariant() const { return last <= 100; }
};

}
