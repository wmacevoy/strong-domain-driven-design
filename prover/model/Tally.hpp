/*
  prover model: a class that indexes memory.  It counts the bytes it sees by their low two
  bits.  What a reader expects: no call reads or writes outside `count`, and `total` is the sum of
  the four counts (as 32-bit numbers, which wrap).
*/
#pragma once
#include <cstdint>

class Tally {
public:
  Tally()
  {
    count[0] = 0;
    count[1] = 0;
    count[2] = 0;
    count[3] = 0;
    total = 0;
  }

  void see(uint8_t byte)
  {
    uint32_t kind = byte & 3;
    count[kind] = count[kind] + 1;
    total = total + 1;
  }

  uint32_t of(uint32_t kind) const
  {
    if (kind >= 4) return 0;
    return count[kind];
  }

  uint32_t getTotal() const
  {
    return total;
  }

  /* The total is the sum of the four counts (32-bit numbers, which wrap). */
  bool invariant() const
  {
    return total == count[0] + count[1] + count[2] + count[3];
  }

private:
  uint32_t count[4];
  uint32_t total;
};
