/*
  prover model: a class that shifts by an amount known only when it runs.  It is a set of
  the numbers 0 to 63, kept as the bits of one word.

  In C++ a shift by the width or more is undefined.  So what is owed of put() and has() includes
  that the amount is below 64, which is why each masks it first.
*/
#pragma once
#include <cstdint>

class Bits {
public:
  Bits()
  {
    word = 0;
  }

  void put(uint64_t n)
  {
    uint64_t one = 1;
    word = word | (one << (n & 63));
  }

  uint64_t has(uint64_t n) const
  {
    return (word >> (n & 63)) & 1;
  }

  bool invariant() const
  {
    return true;
  }

private:
  uint64_t word;
};
