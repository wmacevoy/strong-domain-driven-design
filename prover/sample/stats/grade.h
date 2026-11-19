/*
  prover sample: what a method expects of its caller, said by `pre( condition )` (C++26).

  Nothing tests a precondition when the program runs. It is owed by whoever calls: a method that
  says one is proved given it, and its model has no result where it is not so, so a caller is
  proved safe only if it keeps it.

  Score's constructor expects a number of at most 100, and tests nothing. Board::mark_number makes
  a Score from any number, by taking the remainder first: that the remainder is at most 100 is
  proved of Board, where the Score is made. Shelf::at expects a place that is used; Shelf::first
  calls it only where there is one.
*/
#include "stats/not-here.h"
#include <cstdint>

namespace Stats {

class Score
{
public:
  static const uint32_t MOST = 100;

private:
  uint32_t value;

public:
  explicit Score( uint32_t raw ) pre( raw <= MOST ) : value( raw ) {}

  uint32_t number( void ) const { return value; }

  bool invariant() const { return value <= MOST; }
};

class Board
{
private:
  uint32_t seen[101];
  uint32_t marks;

public:
  Board() : seen(), marks( 0 ) {}

  void mark( Score s )
  {
    seen[s.number()] += 1;
    marks += 1;
  }

  void mark_number( uint32_t n )
  {
    Score s( n % 101 );
    mark( s );
  }

  uint32_t times( Score s ) const { return seen[s.number()]; }

  bool invariant() const { return true; }
};

class Shelf
{
private:
  uint32_t slots[8];
  uint32_t used;

public:
  Shelf() : slots(), used( 0 ) {}

  void add( uint32_t v ) pre( used < 8 )
  {
    slots[used] = v;
    used += 1;
  }

  uint32_t at( uint32_t i ) const pre( i < used ) { return slots[i]; }

  uint32_t first( void ) const
  {
    if ( used == 0 )
      return 0;
    return at( 0 );
  }

  bool invariant() const { return used <= 8; }
};

}
