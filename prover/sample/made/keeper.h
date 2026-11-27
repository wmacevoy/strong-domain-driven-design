/*
  prover sample: a class that makes values of another (made/mark.h) from parts of a view it is
  handed, and copies the bytes of one. Ordinary C++; nothing here knows the tool.
  What is owed: for every view, no memory error (each part handed on is within the view; the copy
  is within both arrays); where a Mark's constructor throws, `keep` throws, and the invariant holds
  either way. The invariant rests on Mark's: a mark's head is zeros, so what is kept begins with them.
*/
#pragma once
#include "made/mark.h"
#include <cstdint>
#include <cstring>
#include <stdexcept>

class Keeper {
public:
  Keeper() : kept(), count( 0 ) {}

  /* Keeps the mark of the first 8 bytes of a message of n, whose rest must be 8 bytes more: throws
     where it is shorter than 8, or its rest is not 8. */
  void keep( const char* p, uint64_t n )
  {
    if ( n < 8 ) {
      throw std::length_error( "a message begins with 8 bytes" );
    }
    Mark head( p, 8 );
    Mark rest( p + 8, n - 8 );
    memcpy( kept, head.data(), 12 );
    count = count + 1;
  }

  uint64_t kept_count() const { return count; }

  bool invariant() const { return kept[0] == 0 && kept[1] == 0 && kept[2] == 0 && kept[3] == 0; }

private:
  unsigned char kept[12];
  uint64_t count;
};
