/* Copyright 2026 Warren D. MacEvoy. MIT (strong-domain-driven-design, LICENSE): one of what the prover trusts, prover/trusted/. */

/*
 * A window on elements that stand one after another, as a type.
 *
 * subarray<iterator>( a, n ) is the n elements from a: at( i ) is *( a + i ), for i below n. So
 * whoever takes one owes nothing but to keep its index below size(): no pointer and length handed
 * over apart, to be believed apart.
 *
 * subarray<iterator, of> is the same, and says by its type what the elements are: of is a name and
 * nothing else (a program's own kind of text: subarray<const unsigned char*, Register>). Nothing reads it:
 * the compiler keeps windows of different kinds apart, and the proofs read every one alike, so
 * what is proved of a reader of bytes is proved of it whatever they are said to be.
 *
 * Making one expects what no test can show when the program runs: that those n elements are
 * there, one after another, and that they stay where they are, unchanged in place, for as long as
 * the subarray exists. That is whoever makes it to keep, and it is held before the program runs
 * (the program's full compile: compile, lint, prove): by proof where a proved class makes one; by the
 * lint, which lets one be only a local or a parameter (never a field, a global or what a
 * function gives back), and lets nothing change what it was made from while it is in scope; and
 * where code that is not proved makes one, by that code, each place listed. at( i ) expects
 * i < size(), which is proved of every reader.
 *
 * fixed<n, of>( a ) is the n bytes from a: a window whose length is its type. at( i ) expects
 * i < n, and a proved class reads one only at an index written out below n (the prover refuses any
 * other), so where a read falls is nothing to prove. Making one expects what making a subarray
 * does, of n bytes; it is made where the length has just been found n.
 *
 * Neither is proved itself: like caller.h they are what the proofs rest on, read by a person. Each
 * keeps a pointer, which no proved class may.
 */

#ifndef STRONG_SUBARRAY_H
#define STRONG_SUBARRAY_H

#include <cstddef>
#include <cstdint>
#include <iterator>

#ifndef __cpp_contracts
#define pre( condition )
#define STRONG_PRE_IS_NOTHING
#endif

namespace Strong {

template <typename Iterator, typename Of = void>
class subarray
{
private:
  Iterator first;
  uint64_t count;

public:
  subarray( Iterator a, uint64_t n ) : first( a ), count( n ) {}

  uint64_t size( void ) const { return count; }

  typename std::iterator_traits<Iterator>::value_type at( uint64_t i ) const pre( i < count ) { return *( first + i ); }
};

template <uint64_t N, typename Of = void>
class fixed
{
private:
  const unsigned char* first;

public:
  explicit fixed( const unsigned char* a ) : first( a ) {}

  uint64_t size( void ) const { return N; }

  unsigned char at( uint64_t i ) const pre( i < N ) { return first[i]; }
};

}

#ifdef STRONG_PRE_IS_NOTHING
#undef pre
#undef STRONG_PRE_IS_NOTHING
#endif

#endif
