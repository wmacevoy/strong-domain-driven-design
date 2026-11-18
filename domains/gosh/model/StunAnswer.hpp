/* Copyright 2026 Warren D. MacEvoy. GPL-3.0-or-later. See github.com/wmacevoy/gosh/LICENSE-GOSH, and LICENSE-MOSH. */

/*
  A model of a domain of gosh: a STUN answer read. It is the logic of gosh's stun_parse
  (src/pathfinding/stun.h, as at gosh commit 1ff1448, 2026-11-16), written again in the subset the
  generator reads: the bytes come from anyone on the Internet, before anything has checked them.

  What a reader expects:
    - parse() ends, and reads nothing outside `data`, whatever the bytes and however many;
    - what it keeps is IPv4 or IPv6 or nothing, and never an IPv6 address of one link alone
      (fe80::/10), nor IPv4 in IPv6's form (::ffff:a.b.c.d), which is kept as the IPv4 it is.

  An answer is: 20 bytes of header (type 0x0101, the body's length, the cookie 0x2112A442, 12 bytes
  of id), then attributes, each a type, a length, the value, and padding to 4 bytes.
*/
#pragma once
#include <cstdint>
#include "Bytes.hpp"

class StunAnswer {
public:
  StunAnswer()
  {
    family = 0;
    port = 0;
    addr[0] = 0;
    addr[1] = 0;
    addr[2] = 0;
    addr[3] = 0;
    addr[4] = 0;
    addr[5] = 0;
    addr[6] = 0;
    addr[7] = 0;
    addr[8] = 0;
    addr[9] = 0;
    addr[10] = 0;
    addr[11] = 0;
    addr[12] = 0;
    addr[13] = 0;
    addr[14] = 0;
    addr[15] = 0;
  }

  /* 1, and where we were seen is kept, if `data` is an answer that says so; else 0, and what is kept is as it was. */
  uint32_t parse(Bytes data)
  {
    uint64_t len = data.size();
    if (len < 20) return 0;
    if (data.at(0) != 0x01 || data.at(1) != 0x01) return 0;
    if (data.at(4) != 0x21 || data.at(5) != 0x12 || data.at(6) != 0xA4 || data.at(7) != 0x42) return 0;
    uint64_t body = ((uint64_t)data.at(2) << 8) | data.at(3);
    if (body > len - 20) return 0;
    uint32_t found = 0;
    uint64_t at = 20;
    while (at + 4 <= 20 + body) {
      uint32_t type = ((uint32_t)data.at(at) << 8) | data.at(at + 1);
      uint64_t size = ((uint64_t)data.at(at + 2) << 8) | data.at(at + 3);
      if (at + 4 + size > 20 + body) break;
      uint64_t v = at + 4;
      if (type == 0x0020 && size >= 20 && data.at(v + 1) == 0x02) {
        /* XOR-MAPPED-ADDRESS for IPv6: disguised with the cookie and the id, bytes 4 to 19 */
        uint32_t port6 = (((uint32_t)data.at(v + 2) << 8) | data.at(v + 3)) ^ 0x2112;
        uint32_t zeros = 1;
        for (uint64_t i = 0; i < 10; i = i + 1) {
          if ((data.at(v + 4 + i) ^ data.at(4 + i)) != 0) zeros = 0;
        }
        uint32_t b0 = data.at(v + 4) ^ data.at(4);
        uint32_t b1 = data.at(v + 5) ^ data.at(5);
        uint32_t b10 = data.at(v + 14) ^ data.at(14);
        uint32_t b11 = data.at(v + 15) ^ data.at(15);
        if (zeros == 1 && b10 == 0xff && b11 == 0xff) {
          /* IPv4 in IPv6's form: the IPv4 address it is */
          family = 4;
          port = port6;
          addr[0] = data.at(v + 16) ^ data.at(16);
          addr[1] = data.at(v + 17) ^ data.at(17);
          addr[2] = data.at(v + 18) ^ data.at(18);
          addr[3] = data.at(v + 19) ^ data.at(19);
          for (uint32_t j = 4; j < 16; j = j + 1) addr[j] = 0;
          found = 1;
        } else if (!(b0 == 0xfe && (b1 & 0xc0) == 0x80)) {
          /* not of one link alone: believed */
          family = 6;
          port = port6;
          for (uint64_t k = 0; k < 16; k = k + 1) addr[k] = data.at(v + 4 + k) ^ data.at(4 + k);
          found = 1;
        }
      }
      /* XOR-MAPPED-ADDRESS, or (from servers of an older kind) MAPPED-ADDRESS; for IPv4 */
      if ((type == 0x0020 || type == 0x0001) && size >= 8 && data.at(v + 1) == 0x01 && !(found == 1 && type == 0x0001)) {
        uint32_t port4 = ((uint32_t)data.at(v + 2) << 8) | data.at(v + 3);
        uint32_t a0 = data.at(v + 4);
        uint32_t a1 = data.at(v + 5);
        uint32_t a2 = data.at(v + 6);
        uint32_t a3 = data.at(v + 7);
        if (type == 0x0020) {
          port4 = port4 ^ 0x2112;
          a0 = a0 ^ 0x21;
          a1 = a1 ^ 0x12;
          a2 = a2 ^ 0xA4;
          a3 = a3 ^ 0x42;
        }
        family = 4;
        port = port4;
        addr[0] = a0;
        addr[1] = a1;
        addr[2] = a2;
        addr[3] = a3;
        for (uint32_t m = 4; m < 16; m = m + 1) addr[m] = 0;
        found = 1;
      }
      at = at + 4 + ((size + 3) & ~(uint64_t)3);
    }
    return found;
  }

  /* 0 for nothing kept, 4 for IPv4, 6 for IPv6. */
  uint32_t getFamily() const
  {
    return family;
  }

  uint32_t getPort() const
  {
    return port;
  }

  /* A byte of the address: 4 of them for IPv4, 16 for IPv6. */
  uint32_t getAddr(uint32_t i) const
  {
    if (i >= 16) return 0;
    return addr[i];
  }

  /* What is kept is nothing, IPv4 or IPv6; and if IPv6, not an address of one link alone (fe80::/10). */
  bool invariant() const
  {
    return (family == 0 || family == 4 || family == 6)
        && !(family == 6 && addr[0] == 0xfe && (addr[1] & 0xc0) == 0x80);
  }

private:
  uint32_t family;
  uint16_t port;
  uint8_t addr[16];
};
