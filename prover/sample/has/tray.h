/*
  prover sample: a drip tray of 40 ml, a part of the station (station.h). What is added must fit.
*/
#pragma once
#include <cstdint>

class Tray
{
public:
  static const uint32_t FULL = 40;

  Tray() : ml( 0 ) {}

  uint32_t held() const { return ml; }

  uint32_t room() const { return FULL - ml; }

  /* n ml of drips: there must be room for them. */
  void add( uint32_t n ) pre( n <= FULL - ml ) { ml = ml + n; }

  void empty() { ml = 0; }

  bool invariant() const { return ml <= FULL; }

private:
  uint32_t ml;
};
