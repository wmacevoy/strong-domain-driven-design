/*
  A proof written as a test that cannot be run.

  A proof here looks like the test a person would write if a machine could run it:

      PROOF( name )
      {
        for ( float limit : all<float>( 0, FLT_MAX ) ) {      every float from 0 to the largest, in turn
          ...
          PROVE( condition );                                 and at each, this holds
        }
      }

  It is C++, and it compiles: so every name and type in it is checked by the compiler, against the
  class itself. It could even be run: all<T>( a, b ) does step through every value of T from a to
  b, both included. But two such loops of float, one inside the other, are 2^62 rounds. Nobody
  runs it. It is read:

    - `for ( T x : all<T>( a, b ) )` says "for every x of T from a to b";
    - what stands in the loop is done to whatever the rounds before left: so what is proved is
      proved of every state those rounds could leave, not of a fresh one each time;
    - `PROVE( condition )` says what must be shown to hold there, every time.

  So a person audits what is claimed by reading a test, in the language of the class, and need
  read nothing else. What shows it is the prover; this header only makes the text compile.

  all<float> leaves out what is not a number, and the infinities: there is none from a to b when
  a and b are finite. That is why a proof says its bounds.
*/
#pragma once
#include <cmath>
#include <cstdlib>
#include <limits>
#include <type_traits>

template <typename T>
class all
{
public:
  all( T from, T to ) : first( from ), last( to ) {}

  class at
  {
  public:
    at( T v, bool p ) : value( v ), past( p ) {}
    T operator*() const { return value; }
    at& operator++()
    {
      if ( value == last_of ) {
        past = true;
      } else {
        value = next( value );
      }
      return *this;
    }
    bool operator!=( const at& other ) const { return past != other.past; }
    T last_of;

  private:
    static T next( T v )
    {
      if constexpr ( std::is_floating_point<T>::value ) {
        return std::nextafter( v, std::numeric_limits<T>::infinity() );
      } else {
        return static_cast<T>( v + 1 );
      }
    }
    T value;
    bool past;
  };

  at begin() const
  {
    at a( first, !( first <= last ) );
    a.last_of = last;
    return a;
  }
  at end() const
  {
    at a( last, true );
    a.last_of = last;
    return a;
  }

private:
  T first, last;
};

/* A proof: a function nobody calls. */
#define PROOF( name ) void proof_##name( void )

/* What must be shown to hold here. (Were the proof ever run, a false one would end it.) */
#define PROVE( condition ) \
  do { \
    if ( !( condition ) ) \
      std::abort(); \
  } while ( 0 )
