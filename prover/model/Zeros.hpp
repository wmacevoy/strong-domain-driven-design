/*
  prover model: a class with a loop over bytes that are not its own.  It counts the bytes
  it is given, and how many of them are zero.

  Its invariant claims nothing (the counts wrap, so nothing simple is always true of them).  What
  is owed is then only what is owed of every class: take() ends, and reads nothing outside `data`.
*/
#pragma once
#include <cstdint>
#include "Bytes.hpp"

class Zeros {
public:
  Zeros()
  {
    zeros = 0;
    seen = 0;
  }

  void take(Bytes data)
  {
    for (uint64_t i = 0; i < data.size(); i = i + 1) {
      if (data.at(i) == 0) zeros = zeros + 1;
      seen = seen + 1;
    }
  }

  uint64_t getZeros() const
  {
    return zeros;
  }

  uint64_t getSeen() const
  {
    return seen;
  }

  bool invariant() const
  {
    return true;
  }

private:
  uint64_t zeros;
  uint64_t seen;
};
