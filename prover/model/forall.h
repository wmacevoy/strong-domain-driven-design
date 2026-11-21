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

  RUN SMALL. Compiled with PROOC_RUN, the same file is a test that can be run, at small bounds:
  each all<T>() of whole numbers steps through its first PROOC_EDGE values and its last PROOC_EDGE,
  and each every_bytes() through a fixed, seeded sample (the short sequences of a few edge bytes,
  then a few of each length). PROVE then says which one is false, and where, and the run ends with
  a failure. prove.sh runs it, with the byte view checked and under the sanitizers, before anything
  is proved: so a claim that is false is found in a second, and what proofs.py makes of the file,
  which nothing else runs, is set against what the file does when it runs. A run that passes shows
  only the values it ran; it proves nothing.
*/
#pragma once
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <limits>
#include <type_traits>
#include <vector>

#ifdef PROOC_RUN
/* How many values at each end of a loop over whole numbers a run takes. */
static const unsigned long long PROOC_EDGE = 8;
#endif

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
        return *this;
      }
#ifdef PROOC_RUN
      if constexpr ( std::is_integral<T>::value && !std::is_same<T, bool>::value ) {
        typedef typename std::make_unsigned<T>::type U;
        taken = taken + 1;
        const U left = static_cast<U>( static_cast<U>( last_of ) - static_cast<U>( value ) );
        if ( taken == PROOC_EDGE && left > PROOC_EDGE ) {
          value = static_cast<T>( static_cast<U>( last_of ) - static_cast<U>( PROOC_EDGE - 1 ) ); /* the last values */
          return *this;
        }
      }
#endif
      value = next( value );
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
#ifdef PROOC_RUN
    unsigned long long taken = 0;
#endif
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
#ifndef PROOC_RUN
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
#else
/* Run small: a fixed sample, the same every run. Every sequence of up to three bytes drawn from a
   few edge values; then, for each length up to 96, four whose bytes are a seeded number's. Of n
   bytes alone: all zero, all 0xff, and 64 seeded ones. */
class every_bytes
{
public:
  every_bytes()
  {
    const unsigned char edge[] = { 0, 1, 0x7f, 0x80, 0xfe, 0xff };
    const size_t e = sizeof( edge );
    samples.push_back( std::vector<unsigned char>() );
    for ( size_t length = 1; length <= 3; length++ ) {
      size_t count = 1;
      for ( size_t k = 0; k < length; k++ ) {
        count = count * e;
      }
      for ( size_t c = 0; c < count; c++ ) {
        std::vector<unsigned char> b( length );
        size_t rest = c;
        for ( size_t k = 0; k < length; k++ ) {
          b[k] = edge[rest % e];
          rest = rest / e;
        }
        samples.push_back( b );
      }
    }
    for ( size_t length = 4; length <= 96; length++ ) {
      for ( int k = 0; k < 4; k++ ) {
        samples.push_back( seeded( length ) );
      }
    }
  }
  explicit every_bytes( size_t length )
  {
    samples.push_back( std::vector<unsigned char>( length, 0 ) );
    samples.push_back( std::vector<unsigned char>( length, 0xff ) );
    for ( int k = 0; k < 64; k++ ) {
      samples.push_back( seeded( length ) );
    }
  }

  std::vector<std::vector<unsigned char> >::const_iterator begin() const { return samples.begin(); }
  std::vector<std::vector<unsigned char> >::const_iterator end() const { return samples.end(); }

private:
  std::vector<unsigned char> seeded( size_t length )
  {
    std::vector<unsigned char> b( length );
    for ( size_t k = 0; k < length; k++ ) {
      seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
      b[k] = static_cast<unsigned char>( seed >> 56 );
    }
    return b;
  }
  unsigned long long seed = 20261121;
  std::vector<std::vector<unsigned char> > samples;
};
#endif

#ifndef PROOC_RUN
/* A proof: a function nobody calls. */
#define PROOF( name ) void proof_##name( void )

/* What must be shown to hold here. (Were the proof ever run, a false one would end it.) */
inline void PROVE( bool holds )
{
  if ( !holds ) {
    std::abort();
  }
}
#else
/* Run small: each proof is called, in the order written; a PROVE that is false says which, and
   where, and the run ends (exit 1). Otherwise main says how many held. */
struct prooc_proof
{
  const char* name;
  void ( *run )( void );
};
inline std::vector<prooc_proof>& prooc_proofs()
{
  static std::vector<prooc_proof> all;
  return all;
}
inline unsigned long long& prooc_held()
{
  static unsigned long long n = 0;
  return n;
}
struct prooc_register
{
  prooc_register( const char* name, void ( *run )( void ) ) { prooc_proofs().push_back( prooc_proof{ name, run } ); }
};
#define PROOF( name ) \
  void proof_##name( void ); \
  static prooc_register prooc_registered_##name( #name, proof_##name ); \
  void proof_##name( void )
inline void prooc_prove( bool holds, const char* what, int line )
{
  if ( !holds ) {
    std::printf( "false when run at small bounds: PROVE( %s ), line %d\n", what, line );
    std::exit( 1 );
  }
  prooc_held() = prooc_held() + 1;
}
#define PROVE( ... ) prooc_prove( ( __VA_ARGS__ ), #__VA_ARGS__, __LINE__ )
int main()
{
  for ( const prooc_proof& p : prooc_proofs() ) {
    p.run();
  }
  std::printf( "%zu proofs run, %llu PROVEs held\n", prooc_proofs().size(), prooc_held() );
  return 0;
}
#endif
