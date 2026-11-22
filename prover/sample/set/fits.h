/*
  prover sample: how many of n fit in room. A domain of one function, used by Jar's proof file.
*/
#pragma once
#include <cstdint>

inline uint32_t fits( uint32_t n, uint32_t room )
{
  if ( n > room ) return room;
  return n;
}
