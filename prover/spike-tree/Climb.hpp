/*
  spike-tree: the smallest class with loops, and nothing else new: a `for` with a local of its
  own, and a `while` over a parameter, with a local that outlives it. No view, no array, no call.
*/
#pragma once
#include <cstdint>
class Climb {
public:
  Climb()
  {
    total = 0;
    steps = 0;
  }
  void add(uint32_t n)
  {
    for (uint32_t i = 0; i < n; i = i + 1) {
      total = total + i;
      steps = steps + 1;
    }
  }
  uint32_t above(uint32_t n)
  {
    uint32_t k = 0;
    while (n > total) {
      n = n - 1;
      k = k + 1;
    }
    return k;
  }
  uint32_t get() const
  {
    return total;
  }
  bool invariant() const
  {
    return true;
  }
private:
  uint32_t total;
  uint32_t steps;
};
