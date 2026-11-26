/* Copyright 2026 Warren D. MacEvoy. MIT (strong-domain-driven-design, LICENSE): one of what the prover trusts, prover/trusted/. */

/*
 * A number that is within its bounds, as a type.
 *
 * bounded<a, b, type> is a `type` from a to b, both included (so that a whole type can be said:
 * bounded<0, UINT64_MAX, uint64_t>). Nothing is tested when one is made or used. Making one from
 * a number is what expects something, of whoever makes it: pre( a <= raw && raw <= b ). After that
 * every use has, for nothing, that the number is within the bounds.
 *
 * "Expects" is C++26's contract. It is proved, not tested (prover/claims/bounded_ofClaims.lean):
 * of this class once, for every type whose values compare by <= and every a and b; and of each
 * class that makes one, that it gives the constructor what it expects. A compiler that knows
 * contracts (g++ 16, -fcontracts) tests it too, and ends the program if it is not so; for any
 * other, `pre` is nothing here, and nothing is tested.
 *
 * For a floating type, a number within finite bounds is not an infinity and is not "not a number":
 * the compiler is asked that the bounds themselves are finite. (A floating bound needs C++20.)
 *
 * Two ways to make one. bounded, for a proved class: nothing tested. bounded_checked, below, for
 * everything else: tested when the program runs, and the process ends if the test fails.
 */

#ifndef STRONG_BOUNDED_H
#define STRONG_BOUNDED_H

#include "caller.h"

#ifndef __cpp_contracts
#define pre( condition )
#define STRONG_PRE_IS_NOTHING
#endif

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
 * The way in from code that is not proved. bounded_checked<a, b, type> is made from any number,
 * and expects nothing: it tests the number, when the program runs, and the process ends if it is
 * not within the bounds, saying who made it (caller.h). So one that exists is within its bounds,
 * as a bounded is; what differs is who may make one, and what that costs. Code that is not proved
 * may not make a bounded itself: the proving refuses the program (prover/ingress.py).
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

#ifdef STRONG_PRE_IS_NOTHING
#undef pre
#undef STRONG_PRE_IS_NOTHING
#endif

#endif
