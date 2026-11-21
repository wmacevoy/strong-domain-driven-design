/* Copyright 2026 Warren D. MacEvoy. GPL-3.0-or-later. See github.com/wmacevoy/gosh/LICENSE-GOSH, and LICENSE-MOSH. */

/*
 * What a REGISTER's opened text is taken for at the meetup, said of every text there is, as a test
 * that cannot be run (prover/model/forall.h says how it is read). It is proved
 * (claims/MeetupRegisterProofClaims.lean).
 *
 * The text is what the cipher gave back for a REGISTER under a ticket: whoever holds the ticket
 * chose it, so it may be anything. What could go wrong is a read past it, and a family kept that
 * no address has, which meetup_addr_of would then not refuse. Every text here has 27 bytes:
 * src/meetup/sealed.h hands a REGISTER's reader no other (a person reads that line).
 *
 * What this does NOT cover: that the time kept is the last eight bytes, most significant first (an
 * equation the proof reader does not yet take); meetup_read_register's own lines, which copy where
 * out; and what Registrations does with the time and where.
 */
#include <cstdint>
#include <vector>

#include "src/strong/meetup/register.h"

#include "forall.h"

/* After any texts of 27 bytes, one after another through the same reader. (That a text has 27 is
   its type, fixed<27, Register>: what is read of any other length is nothing, and is not asked here.) */
PROOF( whatever_is_opened_is_a_register_of_a_family_there_is_or_is_not_read )
{
  Strong::Meetup::Register r;
  for ( const std::vector<unsigned char>& bytes : every_bytes( 27 ) ) {
    /* it ends, and reads nothing outside these bytes: that this call is here says so */
    r.read_checked( Strong::fixed<27, Strong::Meetup::Register>( bytes.data() ) );

    PROVE( r.invariant() );
    PROVE( r.family_checked() == 0 || r.family_checked() == 4 || r.family_checked() == 6 );
  }
}
