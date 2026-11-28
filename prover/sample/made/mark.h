/*
  prover sample: a constructor that tests what it is given, and throws, and makes its array of bytes
  by a fill and a copy; and a second constructor, of a number. Ordinary C++; nothing here knows the
  tool.
  What is owed: the constructor commits no memory error, for every view it is handed; where it does
  not throw, every byte of the array has a value (the generator checks that the fill and the copy
  cover them), and the invariant holds.
*/
#pragma once
#include <cstdint>
#include <cstring>
#include <stdexcept>

class Mark {
public:
  /* 12 bytes: 4 zeros, then the 8 bytes of s. Throws unless s is 8 bytes. */
  Mark( const char* s, uint64_t n )
  {
    if ( n != 8 ) {
      throw std::length_error( "a mark is made of 8 bytes" );
    }
    memset( bytes, 0, 4 );
    memcpy( bytes + 4, s, 8 );
  }

  /* 12 bytes: 11 zeros, then b's lowest byte. */
  Mark( uint32_t b )
  {
    memset( bytes, 0, sizeof( bytes ) );
    bytes[11] = (unsigned char)( b & 255 );
  }

  /* Byte i, or 0 past the end. */
  uint32_t at( uint64_t i ) const
  {
    if ( i >= 12 ) {
      return 0;
    }
    return bytes[i];
  }

  /* Where its 12 bytes begin. */
  const unsigned char* data() const { return bytes; }

  bool invariant() const { return bytes[0] == 0 && bytes[1] == 0 && bytes[2] == 0 && bytes[3] == 0; }

private:
  unsigned char bytes[12];
};
