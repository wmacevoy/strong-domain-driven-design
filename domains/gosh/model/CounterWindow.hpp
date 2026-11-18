/* Copyright 2026 Warren D. MacEvoy. GPL-3.0-or-later. See github.com/wmacevoy/gosh/LICENSE-GOSH, and LICENSE-MOSH. */

/*
  A model of gosh's CounterWindow (src/meetup/registrations.h, at gosh's commit d0cfd4f): which
  counters an end of a ticket has used, of the last 1024.  The meetup's guard against a message
  sent a second time.

  It is gosh's class written again in the subset the generator reads, statement for statement:
    - test(), set() and clear(), gosh's three private helpers, are written out where they are
      called (the generator reads no call);
    - `c % 1024 / 64` is `(c & 1023) >> 6`, and `c % 64` is `c & 63` (it reads no division);
    - `any` is a byte, 0 or 1, and take() gives 1 or 0 (it reads no bool value);
    - memset( seen, 0xff, ... ) is sixteen assignments.
  That this is what gosh's class does is tested, not proved (the project's REQ1/DOM-2).
*/
#pragma once
#include <cstdint>

class CounterWindow {
public:
  CounterWindow()
  {
    any = 0;
    top = 0;
    seen[0] = 0;
    seen[1] = 0;
    seen[2] = 0;
    seen[3] = 0;
    seen[4] = 0;
    seen[5] = 0;
    seen[6] = 0;
    seen[7] = 0;
    seen[8] = 0;
    seen[9] = 0;
    seen[10] = 0;
    seen[11] = 0;
    seen[12] = 0;
    seen[13] = 0;
    seen[14] = 0;
    seen[15] = 0;
  }

  /* 1, and the counter marked used, if it has not been used and is not too far behind. */
  uint8_t take(uint64_t c)
  {
    uint64_t one = 1;
    if (any == 0) {
      any = 1;
      top = c;
      seen[0] = 0xffffffffffffffff; /* everything behind it, as if used */
      seen[1] = 0xffffffffffffffff;
      seen[2] = 0xffffffffffffffff;
      seen[3] = 0xffffffffffffffff;
      seen[4] = 0xffffffffffffffff;
      seen[5] = 0xffffffffffffffff;
      seen[6] = 0xffffffffffffffff;
      seen[7] = 0xffffffffffffffff;
      seen[8] = 0xffffffffffffffff;
      seen[9] = 0xffffffffffffffff;
      seen[10] = 0xffffffffffffffff;
      seen[11] = 0xffffffffffffffff;
      seen[12] = 0xffffffffffffffff;
      seen[13] = 0xffffffffffffffff;
      seen[14] = 0xffffffffffffffff;
      seen[15] = 0xffffffffffffffff;
      return 1;
    }
    if (c > top) {
      for (uint64_t i = top + 1; i <= c && i - top <= 1024; i = i + 1) {
        seen[(i & 1023) >> 6] = seen[(i & 1023) >> 6] & ~(one << (i & 63));
      }
      top = c;
      seen[(c & 1023) >> 6] = seen[(c & 1023) >> 6] | (one << (c & 63));
      return 1;
    }
    if (top - c >= 1024) return 0;
    if (((seen[(c & 1023) >> 6] >> (c & 63)) & 1) != 0) return 0;
    seen[(c & 1023) >> 6] = seen[(c & 1023) >> 6] | (one << (c & 63));
    return 1;
  }

  /* `any` is a flag.  (What the window is for, that no counter is taken twice, is a statement
     about every history of calls, and an invariant of the state cannot say it.) */
  bool invariant() const
  {
    return any <= 1;
  }

private:
  uint8_t any;
  uint64_t top;
  uint64_t seen[16];
};
