/* Copyright 2026 Warren D. MacEvoy. GPL-3.0-or-later. See github.com/wmacevoy/gosh/LICENSE-GOSH, and LICENSE-MOSH. */

/*
 * What a REGISTERED's opened text is taken for at an end, said of every text there is, as a test
 * that cannot be run (prover/model/forall.h says how it is read). It is proved
 * (claims/MeetupRegisteredProofClaims.lean).
 *
 * The text is what the cipher gave back for a REGISTERED under a ticket: whoever holds the ticket
 * chose it, so it may be anything. What could go wrong is a read past it, and a family kept that no
 * address has. Every text here has 19 bytes: src/meetup/sealed.h hands a REGISTERED's reader no
 * other (a person reads that line).
 *
 * What this does NOT cover: meetup_registered_at's own lines, which compare where's bytes where
 * they lie; and what the end does once it is registered.
 */
#include <cstdint>
#include <vector>

#include "src/strong/meetup/registered.h"

#include "forall.h"

/* After any texts of 19 bytes, one after another through the same reader. (That a text has 19 is
   its type, fixed<19, Registered>: what is read of any other length is nothing, and is not asked here.) */
PROOF( whatever_is_opened_says_a_family_there_is_or_is_not_read )
{
  Strong::Meetup::Registered r;
  for ( const std::vector<unsigned char>& bytes : every_bytes( 19 ) ) {
    /* it ends, and reads nothing outside these bytes: that this call is here says so */
    r.read_checked( Strong::fixed<19, Strong::Meetup::Registered>( bytes.data() ) );

    PROVE( r.invariant() );
    PROVE( r.family_checked() == 0 || r.family_checked() == 4 || r.family_checked() == 6 );
  }
}
