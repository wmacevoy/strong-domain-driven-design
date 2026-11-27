/*
  prover sample: a class whose methods are defined in a source file (meter.cc), as most programs
  write them. from/Meter says `defined split/meter.cc`: the definitions of its methods are read
  from there, each as it stands, after the class.
*/
#include <cstdint>

namespace Split {

class Meter
{
private:
  uint32_t reading;
  uint32_t most;

public:
  Meter();
  uint32_t add( uint32_t n );
  uint32_t value( void ) const;
  bool invariant() const { return reading <= most; }
};

}
