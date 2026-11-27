/*
  prover model: bytes copied. Ordinary C++; nothing here knows the tool.
  memcpy into one of the object's arrays of bytes, from a view or from another of its arrays: what
  is owed is that both places are within, for every view and every number it is handed. An array
  of char is bytes that are only copied, never read as numbers.
*/
#pragma once
#include <cstdint>
#include <cstring>

class Stamp {
public:
  Stamp() : head(), tail(), kept( 0 ) {}

  /* Keeps the 8 bytes at `at` of a message of n bytes; false if they are not all there. */
  bool keep( const unsigned char* p, uint64_t n, uint64_t at )
  {
    if ( at > n || n - at < 8 ) {
      return false;
    }
    memcpy( head, p + at, 8 );
    kept = kept + 1;
    return true;
  }

  /* Keeps the first 4 bytes of a text of n, if it has them. */
  void keep_tail( const char* s, uint64_t n )
  {
    if ( n < 4 ) {
      return;
    }
    memcpy( tail, s, 4 );
  }

  /* The head's first n bytes made zeros, if it has n; false if not. */
  bool clear( uint64_t n )
  {
    if ( n > 8 ) {
      return false;
    }
    memset( head, 0, n );
    return true;
  }

  /* The tail's bytes over the head's last 4. */
  void fold() { memcpy( head + 4, tail, 4 ); }

  uint32_t first() const { return head[0]; }

  uint64_t count() const { return kept; }

  bool invariant() const { return true; }

private:
  unsigned char head[8];
  char tail[4];
  uint64_t kept;
};
