/*
  prover sample: a class that takes, and makes, a bounded number.

  Tank::fill takes a Level, a number from 0 to 100, and indexes 101 places by it with no test:
  that it stays inside them is had from the type, which was proved once, of every type and every
  pair of bounds. Tank::fill_number makes a Level from any number; that it is within the bounds is
  owed there, where it is made, and proved of Tank.

  Tank::fill_checked is the way in for code that is not proved. It takes a LevelChecked, which
  anything may make from any number: making it is what tests, and ends the process if the number
  is not within the bounds. So fill_checked expects nothing, and tests nothing more: that it then
  makes a Level rightly is proved from what a LevelChecked is.
*/
#include "strong/bounded.h"
#include <cstdint>

namespace Strong {

static const uint32_t FULL = 100;

typedef bounded<0, FULL, uint32_t> Level;

typedef bounded_checked<0, FULL, uint32_t> LevelChecked;

class Tank
{
private:
  uint32_t marks[101];
  uint32_t level;

public:
  Tank() : marks(), level( 0 ) {}

  void fill( Level to )
  {
    marks[to.number()] += 1;
    level = to.number();
  }

  void fill_number( uint32_t n )
  {
    Level to( n % 101 );
    fill( to );
  }

  void fill_checked( LevelChecked n )
  {
    Level to( n.number() );
    fill( to );
  }

  uint32_t at( void ) const { return level; }

  bool invariant() const { return level <= FULL; }
};

}
