/* Copyright 2026 Warren D. MacEvoy. GPL-3.0-or-later. See github.com/wmacevoy/gosh/LICENSE-GOSH, and LICENSE-MOSH. */

/*
 * What a datagram from anyone at all is taken for at the meetup's door, and at an end's, said of
 * every datagram there is, as a test that cannot be run (prover/model/forall.h says how it is
 * read). It is proved (claims/MeetupHeaderProofClaims.lean).
 *
 * This is the first thing gosh's registrations-fuzzer and finding-fuzzer reach with bytes from
 * anyone: meetup_read_header. What could go wrong there is a read past the datagram; and a head
 * that says a ticket, an end or a sealed part lies where the datagram has no bytes, which
 * whoever copies the ticket out or calls the cipher would then read ("it guards its buffers with
 * an assert alone": meetup/messages.h).
 *
 * What this does NOT cover, and the fuzzers still do: meetup_read_header's own ten lines, which
 * make pointers and text of these numbers; the cipher; and everything a meetup does with a
 * message once it is opened (Registrations).
 */
#include <cstdint>
#include <vector>

#include "src/strong/meetup/header.h"

#include "forall.h"

/* After any datagrams at all, one after another through the same head. */
PROOF( whatever_is_received_is_one_of_the_five_messages_at_its_length_or_is_not_read )
{
  Strong::MeetupHeader head;
  for ( const std::vector<unsigned char>& bytes : every_bytes() ) {
    /* it ends, and reads nothing outside these bytes: that this call is here says so */
    head.read_checked( Strong::Datagram( bytes.data(), bytes.size() ) );

    PROVE( head.invariant() );
    /* a kind there is (0: nothing read), for an end there is */
    PROVE( head.kind_checked() <= 5 && head.end_checked() <= 1 );
    /* a head with a ticket (all but PASSED) is of a datagram of 52 bytes or more: the ticket's
       16 bytes at 9 and the end at 25 are inside it */
    PROVE( head.kind_checked() == 0 || head.kind_checked() == 4 || head.whole_checked() >= 52 );
    /* and what is sealed begins inside the datagram */
    PROVE( head.kind_checked() == 0 || head.sealed_from_checked() < head.whole_checked() );
  }
}

/* And the datagram a head speaks of is the one it was handed: of a new head, each time. */
PROOF( a_head_that_is_read_is_of_the_datagram_it_was_handed )
{
  for ( const std::vector<unsigned char>& bytes : every_bytes() ) {
    Strong::MeetupHeader head;
    head.read_checked( Strong::Datagram( bytes.data(), bytes.size() ) );
    PROVE( head.kind_checked() == 0 || head.whole_checked() == bytes.size() );
  }
}
