/*
  prover model: a method that throws. Ordinary C++; nothing here knows the tool.
  A throw ends the method and tells its caller. The state it leaves is what the method had made
  by then, and what is owed is that it keeps the invariant: take() throws before it changes
  anything, and so it does. What is thrown is made of literals alone, and is not read. An assert
  that is not so ends the process; take()'s never is, and the comparison runs past it every time.
*/
#pragma once
#include <cassert>
#include <cstdint>
#include <stdexcept>

class Ration {
public:
  Ration() : stock( 100 ), taken( 0 ) {}

  /* Takes n of what is left, and says what is left then; throws if there is not that much. */
  uint32_t take( uint32_t n )
  {
    if ( n > stock ) {
      throw std::length_error( "not that much left" );
    }
    stock = stock - n;
    taken = taken + n;
    assert( stock + taken == 100 );   /* never so: it is proved, and the process would end */
    return stock;
  }

  /* Gives back what was taken, all of it; throws if nothing was. */
  void refill()
  {
    if ( taken == 0 ) {
      throw std::logic_error( "nothing to give back" );
    }
    stock = 100;
    taken = 0;
  }

  uint32_t remaining() const { return stock; }

  /* What is left and what was taken make the whole. */
  bool invariant() const { return stock <= 100 && taken <= 100 && stock + taken == 100; }

private:
  uint32_t stock;
  uint32_t taken;
};
