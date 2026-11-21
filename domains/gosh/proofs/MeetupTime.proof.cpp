/* Copyright 2026 Warren D. MacEvoy. GPL-3.0-or-later. See github.com/wmacevoy/gosh/LICENSE-GOSH, and LICENSE-MOSH. */

/*
 * What a TIME's opened text is taken for at an end, said of every text there is, as a test that
 * cannot be run (prover/model/forall.h says how it is read). It is proved
 * (claims/MeetupTimeProofClaims.lean).
 *
 * The text is what the cipher gave back for a TIME under a ticket: whoever holds the ticket chose
 * it, so it may be anything. What could go wrong is a read past it, and a counter kept that no
 * REGISTER can have, which the end would then compare with its own. Every text here has 16 bytes:
 * src/meetup/sealed.h hands a TIME's reader no other (a person reads that line).
 *
 * What this does NOT cover: that the numbers kept are the text's, most significant first (an
 * equation the proof reader does not yet take); meetup_read_time's own lines; and what the end
 * does with the counter and the time.
 */
#include <cstdint>
#include <vector>

#include "src/strong/meetup/time.h"

#include "forall.h"

/* After any texts of 16 bytes, one after another through the same reader. (That a text has 16 is
   its type, fixed<16, Time>: what is read of any other length is nothing, and is not asked here.) */
PROOF( whatever_is_opened_answers_a_counter_there_can_be )
{
  Strong::Meetup::Time r;
  for ( const std::vector<unsigned char>& bytes : every_bytes( 16 ) ) {
    /* it ends, and reads nothing outside these bytes: that this call is here says so */
    r.read_checked( Strong::fixed<16, Strong::Meetup::Time>( bytes.data() ) );

    PROVE( r.invariant() );
    PROVE( r.answering_checked() <= 0x3fffffffffffffffULL ); /* COUNTER_MOST, 2^62 - 1: the proof reader takes no name for a number */
  }
}
