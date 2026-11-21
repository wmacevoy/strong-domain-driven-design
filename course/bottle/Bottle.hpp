/*
  The course's bottle (lessons 1 to 5). It holds some volume, from nothing up to its size.
  Ordinary C++: nothing here knows the prover. What is always true of it is invariant().

  Whole numbers, unsigned, so that every value can be reasoned about: a float may be "not a
  number", and then every comparison with it is false (prover/sample/bottle has that bottle).
*/
#pragma once
#include <cstdint>

class Bottle
{
public:
  Bottle()
  {
    volume = 0;
    maxVolume = 1;
  }

  uint32_t getVolume() const { return volume; }

  uint32_t getMaxVolume() const { return maxVolume; }

  /* What is poured in, or as much of it as fits. */
  void setVolume( uint32_t value )
  {
    if ( value > maxVolume ) {
      value = maxVolume;
    }
    volume = value;
  }

  /* A bottle of another size. What was in it and no longer fits spills out. */
  void setMaxVolume( uint32_t value )
  {
    maxVolume = value;
    if ( volume > maxVolume ) {
      volume = maxVolume;
    }
  }

  /* There is never more in it than it holds. (Never less than nothing: it is unsigned.) */
  bool invariant() const { return volume <= maxVolume; }

private:
  uint32_t volume;
  uint32_t maxVolume;
};
