/* Lesson 6: merge sort, tested three ways. Each is more facts than the last, and none is all of
   them: there are 256^8 inputs of eight bytes, and 256^0 + ... + 256^8 of up to eight.
   Build and run:  c++ -std=c++17 -O2 -I../../vendor/facts mergesort-facts.cpp ../../vendor/facts/facts.cpp -o mergesort-facts && ./mergesort-facts --facts_timeout=300
   (Every input up to three bytes is 16.8 million sorts: about fifteen seconds here, longer than facts waits by default.) */
#include <algorithm>
#include <cstdint>
#include <vector>

#include "MergeSort.hpp"
#include "facts.h"

/* Sorts these bytes with MergeSort; true if what it holds is what std::sort makes of them. */
static bool sorts_as_std_does( const std::vector<uint8_t>& in )
{
  MergeSort s;
  if ( !s.load( Bytes( in.data(), in.size() ) ) ) {
    return false;
  }
  s.sort();
  std::vector<uint8_t> expected = in;
  std::sort( expected.begin(), expected.end() );
  /* Two oracles: what MergeSort says of itself (sorted, and what was given), and std::sort, byte
     by byte. */
  if ( s.outOfOrder() != 0 || s.notAsGiven() != 0 || s.size() != expected.size() ) {
    return false;
  }
  for ( uint64_t i = 0; i < expected.size(); i++ ) {
    if ( s.at( i ) != expected[i] ) {
      return false;
    }
  }
  return true;
}

/* 1. Examples: the cases someone thought of. */
FACTS( Examples )
{
  FACT( sorts_as_std_does( {} ) );
  FACT( sorts_as_std_does( { 7 } ) );
  FACT( sorts_as_std_does( { 2, 1 } ) );
  FACT( sorts_as_std_does( { 3, 1, 2 } ) );
  FACT( sorts_as_std_does( { 5, 5, 5, 5 } ) );                /* all the same */
  FACT( sorts_as_std_does( { 8, 7, 6, 5, 4, 3, 2, 1 } ) );    /* backwards, and the most it takes */
  FACT( sorts_as_std_does( { 0, 255, 0, 255, 1, 254, 1, 254 } ) );
}

/* What it refuses: more than it can hold. */
FACTS( TooMany )
{
  MergeSort s;
  std::vector<uint8_t> nine( 9, 1 );
  FACT( s.load( Bytes( nine.data(), nine.size() ) ) == false );
  FACT( s.size() == 0u );
}

/* 2. Every input there is, up to three bytes long: 1 + 256 + 65,536 + 16,777,216 of them. A
   proof for those lengths, by running them all; four bytes would be four billion more. */
FACTS( EveryInputUpToThree )
{
  uint64_t tried = 0;
  bool all_sorted = true;
  for ( uint32_t length = 0; length <= 3; length++ ) {
    std::vector<uint8_t> in( length, 0 );
    for ( uint64_t k = 0; k < ( uint64_t( 1 ) << ( 8 * length ) ); k++ ) {
      for ( uint32_t i = 0; i < length; i++ ) {
        in[i] = uint8_t( k >> ( 8 * i ) );
      }
      all_sorted = all_sorted && sorts_as_std_does( in );
      tried++;
    }
  }
  FACT( all_sorted );
  FACT( tried == 1u + 256u + 65536u + 16777216u );
}

/* 3. Many inputs of every length up to eight, chosen at random, but seeded: the same every run. */
FACTS( SeededInputsUpToEight )
{
  uint32_t seed = 20261121;
  for ( int round = 0; round < 100000; round++ ) {
    seed = seed * 1664525u + 1013904223u;
    std::vector<uint8_t> in( ( seed >> 24 ) % 9 );
    for ( uint8_t& b : in ) {
      seed = seed * 1664525u + 1013904223u;
      b = uint8_t( seed >> 24 ) % 4; /* few values, so that there are many repeats */
    }
    FACT( sorts_as_std_does( in ), "round " << round );
  }
}

FACTS_REGISTER_ALL()
{
  FACTS_REGISTER( Examples );
  FACTS_REGISTER( TooMany );
  FACTS_REGISTER( EveryInputUpToThree );
  FACTS_REGISTER( SeededInputsUpToEight );
}

FACTS_MAIN
