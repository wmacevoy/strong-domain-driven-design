/*
  prover model: signed arithmetic. Ordinary C++; nothing here knows the tool.
  A frame of n bytes is a head of 8, a body, and a tag of 16 at the body's end. Its lengths are
  worked out in int, as such code often is: n - 8 made an int is n's value modulo 2^32 (C++20), and
  a subtraction of two ints that overflows is undefined, which is owed never to happen. So n is
  bounded first: without the bound, an n near 2^31 makes body_len - 16 overflow.
*/
#pragma once
#include <cstdint>

class Frame {
public:
  Frame() : body( 0 ) {}

  /* The bytes a frame of n carries, the head and the tag taken off; 0 if it is too short or too long. */
  uint64_t carried( uint64_t n )
  {
    if ( n < 24 || n > 65536 ) {
      return 0;
    }
    int body_len = n - 8;
    int pt_len = body_len - 16;
    if ( pt_len < 0 ) {
      return 0;
    }
    body = (uint64_t)body_len;
    return (uint64_t)pt_len;
  }

  uint64_t last_body() const { return body; }

  /* The last body was of a frame of at most 65536. */
  bool invariant() const { return body <= 65528; }

private:
  uint64_t body;
};
