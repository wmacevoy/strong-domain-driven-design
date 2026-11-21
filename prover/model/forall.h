/*
  A proof written as a test that cannot be run.

  A proof here looks like the test a person would write if a machine could run it:

      PROOF( name )
      {
        for ( uint32_t limit : all<uint32_t>() ) {            every uint32_t there is, in turn
          ...
          PROVE( condition );                                 and at each, this holds
        }
      }

  It is C++, and it compiles: so every name and type in it is checked by the compiler, against the
  class itself. It could even be run: all<T>() does step through every value of T, and
  all<T>( a, b ) through every one from a to b, both included. But two such loops of 32 bits, one
  inside the other, are 2^64 rounds. Nobody runs it. It is read (proofs.py), as it would run:

    - `for ( T x : all<T>() )` says "for every x of T";
    - `PROVE( condition )` says what must be shown to hold there, every time;
    - a call of a method says that it ends, and reads and writes nothing outside what it is
      given: that too must be shown, for the call to stand in a proof;
    - what stands in a loop is done to whatever the rounds before left. A round knows of the
      rounds before only this: the class's own invariant, and what the loop's last PROVEs say
      without naming the loop's own variable (those are true when the next round begins). So
      what a later round rests on is written, as a PROVE at the end of the loop.

  If every statement the prover makes of this is proved, then every PROVE would hold in every
  round, were it run. So a person audits what is claimed by reading a test, in the language of
  the class, and need read nothing else. This header only makes the text compile.

  all<float> leaves out what is not a number, and the infinities: there is none from a to b when
  a and b are finite. That is why a proof says its bounds.
*/
#pragma once
#include <cmath>
#include <cstdlib>
#include <limits>
#include <type_traits>
#include <vector>

template <typename T>
class all
{
public:
  all() : first( std::numeric_limits<T>::lowest() ), last( std::numeric_limits<T>::max() ) {}
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

/*
  Every sequence of bytes there is, of every length, the shortest first: none, then the 256 of one
  byte, then the 65,536 of two, and so on. A loop over it has no end at all.
      for ( const std::vector<unsigned char>& bytes : every_bytes() )
  Or every sequence of n bytes alone, every_bytes( n ): what a fixed window of n is made of.
      for ( const std::vector<unsigned char>& bytes : every_bytes( 16 ) )
*/
class every_bytes
{
public:
  every_bytes() : whole( false ), n( 0 ) {}
  explicit every_bytes( size_t length ) : whole( true ), n( length ) {}

  class at
  {
  public:
    at( bool of_n, size_t length ) : bytes( length, 0 ), of_n( of_n ), done( false ) {}
    const std::vector<unsigned char>& operator*() const { return bytes; }
    at& operator++()
    {
      for ( size_t i = 0; i < bytes.size(); i++ ) {
        if ( ++bytes[i] != 0 ) {
          return *this;
        }
      }
      if ( of_n ) {
        done = true; /* all of this length are done, and there is no other */
      } else {
        bytes.push_back( 0 ); /* all of this length are done: the first of the next */
      }
      return *this;
    }
    bool operator!=( const at& ) const { return !done; }

  private:
    std::vector<unsigned char> bytes;
    bool of_n, done;
  };

  at begin() const { return at( whole, n ); }
  at end() const { return at( whole, n ); }

private:
  bool whole;
  size_t n;
};

/* A proof: a function nobody calls. */
#define PROOF( name ) void proof_##name( void )

/* What must be shown to hold here. (Were the proof ever run, a false one would end it.) */
inline void PROVE( bool holds )
{
  if ( !holds ) {
    std::abort();
  }
}
