/* Copyright 2026 Warren D. MacEvoy. GPL-3.0-or-later. See github.com/wmacevoy/gosh/LICENSE-GOSH, and LICENSE-MOSH. */

/*
 * What gosh's stun-fuzzer.cc tries of the reader of STUN answers, said of every datagram there
 * is, as a test that cannot be run (prover/model/forall.h says how it is read). It is proved
 * (claims/StunAnswerProofClaims.lean), so for the reader the fuzzing does not matter.
 *
 * The fuzzer hands stun_parse bytes "from anyone at all on the Internet", a few thousand of them
 * a second, and watches for two things:
 *   1. under AddressSanitizer, a read past the end of an exact copy of the bytes;
 *   2. an answer that is taken, and is not an address that can be written down and read back.
 *      That found one on 2026-11-16: an IPv6 address of one link alone (fe80::/10), which cannot
 *      be written without naming the link. The reader has refused those since, and its
 *      invariant says so.
 *
 * Here both are said of every sequence of bytes of every length, after any number of datagrams
 * before it. A call in a proof says more than it shows: that it ends, and reads and writes
 * nothing outside what it is given.
 *
 * What this does NOT cover, and the fuzzer still does: stun_parse's own 20 lines, which make a
 * socket address of what was kept; and format_ip_port and parse_ip_port, which write it down and
 * read it back. Those are not proved.
 */
#include <cstdint>
#include <vector>

#include "src/strong/pathfinding/stunanswer.h"

#include "forall.h"

PROOF( whatever_is_received_is_read_safely_and_what_is_kept_is_an_address )
{
  Strong::Pathfinding::StunAnswer answer;
  for ( const std::vector<unsigned char>& bytes : every_bytes() ) {
    /* (1) it ends, and reads nothing outside these bytes: that this call is here says so */
    answer.parse_checked( Strong::Datagram( bytes.data(), bytes.size() ) );

    /* (2) what is kept is nothing, or IPv4, or IPv6 that is not of one link alone (the invariant) */
    PROVE( answer.invariant() );
    PROVE( answer.kept_family_checked() == 0 || answer.kept_family_checked() == 4 || answer.kept_family_checked() == 6 );
  }
}
