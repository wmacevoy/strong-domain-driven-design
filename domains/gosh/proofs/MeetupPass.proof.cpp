/* Copyright 2026 Warren D. MacEvoy. GPL-3.0-or-later. See github.com/wmacevoy/gosh/LICENSE-GOSH, and LICENSE-MOSH. */

/*
 * What a PASS's opened text is taken for at the meetup, said of every text there is, as a test that
 * cannot be run (prover/model/forall.h says how it is read). It is proved
 * (claims/MeetupPassProofClaims.lean).
 *
 * The text is what the cipher gave back for a PASS under a ticket: whoever holds the ticket chose
 * it, so it may be anything, of any length. What could go wrong is a read past it, and a length
 * kept that is not the text's, or is more than a datagram may be.
 *
 * What this does NOT cover: that what is sent on is these bytes (src/meetup/sealed.h's read_onto,
 * and meetup_passed, read by a person); and what Registrations does with it.
 */
#include <cstdint>
#include <vector>

#include "src/strong/meetup/pass.h"

#include "forall.h"

/* After any texts at all, one after another through the same reader. */
PROOF( whatever_is_opened_is_a_datagram_of_1500_bytes_at_most_or_is_not_read )
{
  Strong::Meetup::Pass p;
  for ( const std::vector<unsigned char>& bytes : every_bytes() ) {
    /* it ends, and reads nothing outside these bytes: that this call is here says so */
    p.read_checked( Strong::Opened<Strong::Meetup::Pass>( bytes.data(), bytes.size() ) );

    PROVE( p.invariant() );
    PROVE( p.length_checked() <= 1500 );
  }
}

/* And the length a pass keeps is of the text it was handed: of a new pass, each time. */
PROOF( a_pass_that_is_read_is_of_the_text_it_was_handed )
{
  for ( const std::vector<unsigned char>& bytes : every_bytes() ) {
    Strong::Meetup::Pass p;
    p.read_checked( Strong::Opened<Strong::Meetup::Pass>( bytes.data(), bytes.size() ) );
    PROVE( p.length_checked() == 0 || p.length_checked() == bytes.size() );
  }
}
