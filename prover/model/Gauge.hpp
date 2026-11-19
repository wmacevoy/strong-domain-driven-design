/*
  prover model: SizedBottle with whole numbers.  Ordinary C++; nothing here knows the tool.
  What is always true of it is invariant(): what must be proven is derived from that, and from the methods.
*/
#pragma once
#include <cstdint>

class Gauge {
public:
  Gauge()
  {
    level = 0;
    limit = 1;
  }

  uint32_t get() const
  {
    return level;
  }

  uint32_t getLimit() const
  {
    return limit;
  }

  void set(uint32_t value)
  {
    if (value > limit) value = limit;
    level = value;
  }

  void setLimit(uint32_t value)
  {
    limit = value;
    if (level > value) level = value;   /* keep level <= limit */
  }

  /* The level is never above the limit. */
  bool invariant() const
  {
    return level <= limit;
  }

private:
  uint32_t level;
  uint32_t limit;
};
