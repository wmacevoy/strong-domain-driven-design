/*
  prover sample: a jar of at most 100 beans. With fits (fits.h) it is a set of two domains, and
  proofs/Jar.proof.cpp is a proof of the set: it makes two jars and calls the function.
*/
#pragma once
#include <cstdint>

class Jar
{
public:
  Jar() { beans = 0; }

  /* Beans poured in, as many as there is room for. */
  void add( uint32_t n )
  {
    uint32_t room = 100 - beans;
    if ( n > room ) {
      n = room;
    }
    beans = beans + n;
  }

  uint32_t count() const { return beans; }

  bool invariant() const { return beans <= 100; }

private:
  uint32_t beans;
};
