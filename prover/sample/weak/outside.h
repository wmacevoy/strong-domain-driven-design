/*
  prover sample: code that is not proved, which uses a class that is.

  Nothing here is read by the generator. It may come in to Tank only by what expects nothing of
  its caller: a LevelChecked, made from any number, and Tank::fill_checked. Were it to make a
  Level itself, nothing would test the number and nothing would prove it: ingress.py refuses that.
*/
#include "strong/tank.h"

namespace Strong {

inline bool from_outside( Tank& tank, uint32_t anything )
{
  if ( anything > 100 )
    return false;                             /* its own test: else the next line ends the process */
  tank.fill_checked( LevelChecked( anything ) );
  return true;
}

}
