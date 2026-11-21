/*
  The course's merge sort (lessons 6 to 9). It sorts up to N bytes, given as a view, and keeps what
  it was given, so that it can say of itself whether what it holds is sorted, and whether it is
  what it was given in another order. Ordinary C++ in the subset the prover reads (lesson 4):
  bottom-up, since a method may not call itself yet; the scratch space a field, since a local
  array is not read yet; every number unsigned.
*/
#pragma once
#include <cstdint>
#include <cstring>

#include "Bytes.hpp"

/* pre( condition ) is C++26's: what a method expects of its caller. Before C++26 it is nothing
   here, and the prover still reads it (lesson 7). */
#ifndef __cpp_contracts
#define pre( condition )
#endif

class MergeSort
{
public:
  static const uint64_t N = 8;

  MergeSort() : data(), original(), scratch(), count( 0 ) {}

  /* Takes these bytes to sort, if there are at most N of them; else false, and nothing changes. */
  bool load( Bytes in )
  {
    if ( in.size() > N ) {
      return false;
    }
    for ( uint64_t i = 0; i < in.size(); i = i + 1 ) {
      data[i] = in.at( i );
      original[i] = in.at( i );
    }
    count = in.size();
    return true;
  }

  uint64_t size() const { return count; }

  /* The byte held at i. */
  uint8_t at( uint64_t i ) const pre( i < count ) { return data[i]; }

private:
  /* data[lo, mid) and data[mid, hi), each sorted, become data[lo, hi), sorted. */
  void merge( uint64_t lo, uint64_t mid, uint64_t hi ) pre( lo <= mid && mid <= hi && hi <= N )
  {
    uint64_t i = lo;
    uint64_t j = mid;
    uint64_t k = lo;
    while ( k < hi ) {
      if ( i < mid && ( j >= hi || data[i] <= data[j] ) ) {
        scratch[k] = data[i];
        i = i + 1;
      } else {
        scratch[k] = data[j];
        j = j + 1;
      }
      k = k + 1;
    }
    for ( k = lo; k < hi; k = k + 1 ) {
      data[k] = scratch[k];
    }
  }

public:
  /* Runs of width 1, 2, 4, ... each merged with the next, until one run is all of them. */
  void sort()
  {
    for ( uint64_t width = 1; width < count; width = width * 2 ) {
      for ( uint64_t lo = 0; lo < count; lo = lo + 2 * width ) {
        uint64_t mid = lo + width;
        if ( mid > count ) {
          mid = count;
        }
        uint64_t hi = lo + 2 * width;
        if ( hi > count ) {
          hi = count;
        }
        merge( lo, mid, hi );
      }
    }
  }

  /* How many bytes held are greater than the next: 0 is sorted. */
  uint64_t outOfOrder() const
  {
    uint64_t pairs = 0;
    for ( uint64_t i = 1; i < count; i = i + 1 ) {
      if ( data[i - 1] > data[i] ) {
        pairs = pairs + 1;
      }
    }
    return pairs;
  }

  /* How many of the 256 values are held a different number of times than they were given: 0 is
     what was given, in another order. */
  uint64_t notAsGiven() const
  {
    uint64_t values = 0;
    for ( uint64_t v = 0; v < 256; v = v + 1 ) {
      uint64_t now = 0;
      uint64_t then = 0;
      for ( uint64_t i = 0; i < count; i = i + 1 ) {
        if ( data[i] == v ) {
          now = now + 1;
        }
        if ( original[i] == v ) {
          then = then + 1;
        }
      }
      if ( now != then ) {
        values = values + 1;
      }
    }
    return values;
  }

  bool invariant() const { return count <= N; }

private:
  uint8_t data[N];
  uint8_t original[N];
  uint8_t scratch[N];
  uint64_t count;
};
