/* Copyright 2026 Warren D. MacEvoy. GPL-3.0-or-later. See github.com/wmacevoy/gosh/LICENSE-GOSH, and LICENSE-MOSH. */

/*
 * What a TIME's opened text is taken for at an end, said of every text there is, as a test that
 * cannot be run (prover/model/forall.h says how it is read). It is proved
 * (claims/MeetupTimeProofClaims.lean).
 *
 * The text is what the cipher gave back for a TIME under a ticket: whoever holds the ticket chose
 * it, so it may be anything. What could go wrong is a read past it, and a counter kept that no
 * REGISTER can have, which the end would then compare with its own.
 *
 * What this does NOT cover: that the numbers kept are the text's, most significant first (an
 * equation the proof reader does not yet take); meetup_read_time's own lines; and what the end
 * does with the counter and the time.
 */
#include <cstdint>
#include <vector>

#include "src/strong/meetup/time.h"

#include "forall.h"

/* After any texts at all, one after another through the same reader. */
PROOF( whatever_is_opened_answers_a_counter_there_can_be )
{
  Strong::Meetup::Time r;
  for ( const std::vector<unsigned char>& bytes : every_bytes() ) {
    /* it ends, and reads nothing outside these bytes: that this call is here says so */
    r.read_checked( Strong::Opened<Strong::Meetup::Time>( bytes.data(), bytes.size() ) );

    PROVE( r.invariant() );
    PROVE( r.answering_checked() <= 0x3fffffffffffffffULL ); /* COUNTER_MOST, 2^62 - 1: the proof reader takes no name for a number */
  }
}

/* And anything but zeros is kept only from a text of 16 bytes: of a new reader, each time. */
PROOF( a_time_that_is_read_is_of_a_text_of_16_bytes )
{
  for ( const std::vector<unsigned char>& bytes : every_bytes() ) {
    Strong::Meetup::Time r;
    r.read_checked( Strong::Opened<Strong::Meetup::Time>( bytes.data(), bytes.size() ) );
    PROVE( ( r.answering_checked() == 0 && r.time_checked() == 0 ) || bytes.size() == 16 );
  }
}
