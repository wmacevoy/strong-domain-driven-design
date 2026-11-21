/*
  Lesson 8: what "my merge sort is correct" means, as a test that cannot be run. For every
  sequence of bytes there is (every_bytes(): every length, every value; no end at all), once it
  is loaded and sorted, what is held is sorted, and it is what was given, in another order.
*/
#include <cstdint>
#include <vector>

#include "MergeSort.hpp"
#include "forall.h"

PROOF( merge_sort_sorts_and_loses_nothing )
{
  for ( const std::vector<unsigned char>& bytes : every_bytes() ) {
    MergeSort s;
    s.load( Bytes( bytes.data(), bytes.size() ) );
    s.sort();
    PROVE( s.invariant() );
    PROVE( s.outOfOrder() == 0 );
    PROVE( s.notAsGiven() == 0 );
  }
}
