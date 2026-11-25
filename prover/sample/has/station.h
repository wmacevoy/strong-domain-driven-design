/*
  prover sample: a class that has-a two proved classes, and keeps a rule that spans them.

  A shot takes 30 ml of water from the tank and drips 10 ml into the tray. Neither part knows of
  the other, or of shots: each promises only its own invariant, and expects of its caller what its
  `pre` says. The station is the one home of the rules that span them:

  - a shot is pulled only if the tank has the water and the tray the room (each part's `pre`:
    what the station owes each part, so that `pull` is safe);
  - the tray holds exactly the drips of the shots pulled since it was emptied (the invariant,
    which spans the station's count and the tray).

  Each part is proved alone. The station is proved from what each part's model does, and is given
  each part's invariant: what is owed of it is owed of every station whose parts keep their own.
*/
#pragma once
#include "has/water.h"
#include "has/tray.h"
#include <cstdint>

class Station
{
public:
  static const uint32_t SHOT = 30;      /* ml of water a shot takes */
  static const uint32_t DRIP = 10;      /* of it, what lands in the tray */

  Station() : water(), tray(), shots( 0 ) {}

  /* A shot, if the water and the tray allow one: 1 if it is pulled, 0 if not. */
  uint32_t pull()
  {
    if ( water.level() < SHOT || tray.room() < DRIP ) return 0;
    water.take( SHOT );
    tray.add( DRIP );
    shots = shots + 1;
    return 1;
  }

  void emptyTray()
  {
    tray.empty();
    shots = 0;
  }

  void refill() { water.fill(); }

  uint32_t pulled() const { return shots; }

  bool invariant() const { return shots <= Tray::FULL / DRIP && tray.held() == shots * DRIP; }

private:
  Water water;
  Tray tray;
  uint32_t shots;
};
