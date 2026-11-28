/*
  prover sample: a method that gives back a value of a class the prover does not read (made/note.h),
  made of a value of a proved class and of bytes: a std::string of n bytes from a place. What is
  owed of what it gives back is that those bytes are there, in the view or in the array they are
  taken from; what the class does with them is not read. Ordinary C++; nothing here knows the tool.
*/
#pragma once
#include "made/mark.h"
#include "made/note.h"
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <string>

class Opener {
public:
  Opener() : last(), opened( 0 ) {}

  /* A message of n bytes: its first 8 are its mark, the rest its text. Throws where it is shorter than 8. */
  const Note open( const char* p, uint64_t n )
  {
    if ( n < 8 ) {
      throw std::length_error( "a message begins with 8 bytes" );
    }
    Mark mark( p, 8 );
    opened = opened + 1;
    const Note ret( mark, std::string( p + 8, n - 8 ) );
    return ret;
  }

  /* The text of the last 16 bytes kept, of n of them. */
  const Note again( uint64_t n )
  {
    if ( n > 16 ) {
      throw std::length_error( "16 bytes are kept" );
    }
    Mark mark( last, 8 );
    const Note ret( mark, std::string( last, n ) );
    return ret;
  }

  uint64_t count() const { return opened; }

  bool invariant() const { return true; }

private:
  char last[16];
  uint64_t opened;
};
