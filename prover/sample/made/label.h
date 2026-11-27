/*
  prover sample: 12 bytes made of a number, its highest byte first (`htobe64`), or of 8 bytes it is
  handed; read back as the number (`be64toh`). It says no invariant, and one method gives a
  std::string, which the prover does not read: it is read for some of it only (from/Label: `only
  Label data number`, its constructors and two methods). Ordinary C++; nothing here knows the tool.
  What is owed: no memory error, for every number and every view.
*/
#pragma once
#include <endian.h>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <string>

class Label {
public:
  /* 4 zeros, then v's 8 bytes, the highest first. */
  Label( uint64_t v )
  {
    uint64_t big = htobe64( v );
    memset( bytes, 0, 4 );
    memcpy( bytes + 4, &big, 8 );
  }

  /* 4 zeros, then the 8 bytes of s. Throws unless s is 8 bytes. */
  Label( const char* s, uint64_t n )
  {
    if ( n != 8 ) {
      throw std::length_error( "a label is made of 8 bytes" );
    }
    memset( bytes, 0, 4 );
    memcpy( bytes + 4, s, 8 );
  }

  /* Its last 8 bytes, as text. */
  std::string text() const { return std::string( bytes + 4, 8 ); }

  /* Where its 12 bytes begin. */
  const char* data() const { return bytes; }

  /* Its last 8 bytes, as the number they are, the highest first. */
  uint64_t number() const
  {
    uint64_t v;
    memcpy( &v, bytes + 4, 8 );
    return be64toh( v );
  }

private:
  char bytes[12];
};
