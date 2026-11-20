/* Copyright 2026 Warren D. MacEvoy. GPL-3.0-or-later. See github.com/wmacevoy/gosh/LICENSE-GOSH, and LICENSE-MOSH. */

/*
 * What a REGISTER's opened text is taken for at the meetup, said of every text there is, as a test
 * that cannot be run (prover/model/forall.h says how it is read). It is proved
 * (claims/MeetupRegisterProofClaims.lean).
 *
 * The text is what the cipher gave back for a REGISTER under a ticket: whoever holds the ticket
 * chose it, so it may be anything. What could go wrong is a read past it, and a family kept that
 * no address has, which meetup_addr_of would then not refuse.
 *
 * What this does NOT cover: that the time kept is the last eight bytes, most significant first (an
 * equation the proof reader does not yet take); meetup_read_register's own lines, which copy where
 * out; and what Registrations does with the time and where.
 */
#include <cstdint>
#include <vector>

#include "src/strong/meetup/register.h"

#include "forall.h"

/* After any texts at all, one after another through the same reader. */
PROOF( whatever_is_opened_is_a_register_of_a_family_there_is_or_is_not_read )
{
  Strong::MeetupRegister r;
  for ( const std::vector<unsigned char>& bytes : every_bytes() ) {
    /* it ends, and reads nothing outside these bytes: that this call is here says so */
    r.read_checked( Strong::Opened<Strong::MeetupRegister>( bytes.data(), bytes.size() ) );

    PROVE( r.invariant() );
    PROVE( r.family_checked() == 0 || r.family_checked() == 4 || r.family_checked() == 6 );
  }
}

/* And a text that is read is one of 27 bytes: of a new reader, each time. */
PROOF( a_register_that_is_read_is_of_a_text_of_27_bytes )
{
  for ( const std::vector<unsigned char>& bytes : every_bytes() ) {
    Strong::MeetupRegister r;
    r.read_checked( Strong::Opened<Strong::MeetupRegister>( bytes.data(), bytes.size() ) );
    PROVE( r.family_checked() == 0 || bytes.size() == 27 );
  }
}
