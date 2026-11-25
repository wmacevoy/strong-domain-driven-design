/*
  prover sample: a water tank of 1,000 ml, a part of the station (station.h). It promises only
  what it is: what is taken must be there, and it never holds more than it is full.
*/
#pragma once
#include <cstdint>

class Water
{
public:
  static const uint32_t FULL = 1000;

  Water() : ml( FULL ) {}

  uint32_t level() const { return ml; }

  /* n ml taken out: they must be there. */
  void take( uint32_t n ) pre( n <= ml ) { ml = ml - n; }

  void fill() { ml = FULL; }

  bool invariant() const { return ml <= FULL; }

private:
  uint32_t ml;
};
