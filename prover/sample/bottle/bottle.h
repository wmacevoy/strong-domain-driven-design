/*
  prover sample: a bottle. It holds some volume, from nothing up to its size.
  Ordinary C++; nothing here knows the tool. What is always true of it is invariant().

  Its numbers are floats. A size, or a volume put in, that is not a number would break it (every
  comparison with one is false): so it expects numbers from 0 up, and bottle.proof.cpp says so by
  the bounds it proves between.
*/
#pragma once

class Bottle
{
public:
  /* Expects 0 <= size, and that size is a number. */
  explicit Bottle( float size ) : max_volume( size ), volume( 0 ) {}

  float getVolume() const { return volume; }

  float getMaxVolume() const { return max_volume; }

  /* What is put in, or as much of it as fits. Expects that value is a number. */
  void setVolume( float value )
  {
    if ( value < 0 ) {
      value = 0;
    }
    if ( value > max_volume ) {
      value = max_volume;
    }
    volume = value;
  }

  /* There is never less than nothing in it, and never more than it holds. */
  bool invariant() const { return 0 <= volume && volume <= max_volume; }

private:
  float max_volume;
  float volume;
};
