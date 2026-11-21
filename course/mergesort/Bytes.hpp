/*
  The byte view: a pointer and a length, read only. The one way a model class reads memory that is
  not its own. Written by hand, once; a model takes it as a parameter and may not keep it.

  at(i) does not check i: a model's safety proof is what says i < size(), on every path. Built with
  PROOC_CHECKED it aborts instead, so that a run can show a proof and the program disagreeing.

  size() is below 2^63: no object in C++ is larger (PTRDIFF_MAX). The model assumes it.
*/
#pragma once
#include <cstdint>
#ifdef PROOC_CHECKED
#include <cstdlib>
#endif

class Bytes {
public:
  Bytes(const uint8_t *data, uint64_t size) : data_(data), size_(size) {}

  uint64_t size() const { return size_; }

  uint8_t at(uint64_t i) const
  {
#ifdef PROOC_CHECKED
    if (i >= size_) std::abort();
#endif
    return data_[i];
  }

private:
  const uint8_t *data_;
  uint64_t size_;
};
