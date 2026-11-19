/*
  prover sample: a number that is within its bounds, as a type.

  bounded<a, b, type> is a `type` from a to b, both included (so that a whole type can be said:
  bounded<0, UINT64_MAX, uint64_t>). Nothing is tested when one is made or used. Making one from a
  number is what expects something, of whoever makes it: pre( a <= raw && raw <= b ). After that
  every use has, for nothing, that the number is within the bounds.

  It is proved once: of every type whose values compare by <=, and of every a and b. For an
  integer that is all there is to say. For a floating type, a number within finite bounds is not
  an infinity and is not "not a number" (no comparison with that is true): the compiler is asked
  that the bounds themselves are finite, and that they follow is IEEE 754's to say, not proved here.
*/
#include "strong/caller.h"
#include <cstdint>

namespace Strong {

template <typename T, T A, T B>
class bounded_of
{
  static_assert( A - A == 0 && B - B == 0, "a bound that is not a finite number" );

private:
  T value;

public:
  explicit bounded_of( T raw ) pre( A <= raw && raw <= B ) : value( raw ) {}

  T number( void ) const { return value; }

  bool invariant() const { return A <= value && value <= B; }
};

/* The same, as it is said: the bounds first. A bound that the type cannot hold exactly does not compile. */
template <auto A, auto B, typename T> using bounded = bounded_of<T, T{ A }, T{ B }>;

/*
  The way in from code that is not proved. bounded_checked<a, b, type> is made from any number,
  and expects nothing: it tests the number, when the program runs, and the process ends if it is
  not within the bounds, saying who made it (caller.h). So one that exists is within its bounds,
  as a bounded is; what differs is who may make it, and what that costs.
*/
template <typename T, T A, T B>
class bounded_checked_of
{
  static_assert( A - A == 0 && B - B == 0, "a bound that is not a finite number" );

private:
  T value;

public:
  explicit bounded_checked_of( T raw, caller from = caller() ) : value( raw )
  {
    STRONG_CHECK( A <= raw && raw <= B, from );
  }

  T number( void ) const { return value; }

  bool invariant() const { return A <= value && value <= B; }
};

template <auto A, auto B, typename T> using bounded_checked = bounded_checked_of<T, T{ A }, T{ B }>;

}
