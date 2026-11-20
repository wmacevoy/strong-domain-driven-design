/* Copyright 2026 Warren D. MacEvoy. GPL-3.0-or-later. See github.com/wmacevoy/gosh/LICENSE-GOSH, and LICENSE-MOSH. */

/*
 * What a meetup message is sealed with, said of every nonce there is, as a test that cannot be
 * run (prover/model/forall.h says how it is read). It is proved (claims/MeetupNonceProofClaims.lean).
 *
 * Why it matters: a ticket's key is used by four senders (each end, and the meetup to each), and
 * the cipher is safe only if no two messages under one key are sealed with the same nonce. A
 * nonce is a sender and that sender's counter. These two say that writing and reading one lose
 * nothing, either way. So two senders never make the same nonce, whatever their counters; and
 * one sender makes the same nonce twice only by using a counter twice.
 *
 * What this does NOT cover: that a sender's counter is below 2^62 and is never used twice (each
 * side starts it from the time of day: FINDINGS, 2026-11-19); the cipher; and meetup_seal's and
 * meetup_open's own lines, which hand these numbers to the cipher.
 */
#include <cstdint>

#include "src/strong/meetup/nonce.h"

#include "forall.h"

/* Every nonce there is says one sender and one counter, and they write that same nonce. So two
   nonces that are read as the same sender and counter are the same nonce. */
PROOF( every_nonce_reads_as_a_sender_and_a_counter_that_write_it_again )
{
  for ( uint64_t sealed_with : all<uint64_t>() ) {
    Strong::Meetup::Nonce nonce;
    nonce.read_checked( sealed_with );
    PROVE( nonce.invariant() );
    PROVE( nonce.end_checked() <= 1 && nonce.by_meetup_checked() <= 1 && nonce.counter_checked() <= 0x3fffffffffffffff );
    PROVE( nonce.value_checked() == sealed_with );
  }
}

/* Every sender there is (two ends; sealed by the end, or by the meetup for it) and every counter
   of 62 bits, written as a nonce and read again, are that sender and that counter. So two
   senders, or two counters of one sender, never write the same nonce. */
PROOF( a_sender_and_a_counter_written_as_a_nonce_are_read_again_as_themselves )
{
  for ( uint32_t an_end : all<uint32_t>( 0, 1 ) ) {
    for ( uint32_t by_meetup : all<uint32_t>( 0, 1 ) ) {
      for ( uint64_t counter : all<uint64_t>( 0, 0x3fffffffffffffff ) ) {
        Strong::Meetup::Nonce nonce;
        nonce.set_checked( an_end, by_meetup, counter );
        nonce.read_checked( nonce.value_checked() );
        PROVE( nonce.end_checked() == an_end && nonce.by_meetup_checked() == by_meetup && nonce.counter_checked() == counter );
      }
    }
  }
}
