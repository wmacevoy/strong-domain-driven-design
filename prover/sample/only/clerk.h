/*
  prover sample: a class read for some of its methods only. Clerk says no invariant, so what is
  owed of a method holds from any state, and the rest of the class need not be read: its
  constructor (which takes a std::string), its destructor, its other methods, and the fields no
  read method names (from/Clerk: `only note`). It cannot be made here as the C++ makes it, so it is
  not compared with the C++, and what is proved says so.
*/
#include <cstdint>
#include <cstdlib>
#include <string>

namespace Only {

class Clerk
{
public:
  static const int ROOM = 16;

private:
  std::string name;
  unsigned char* scratch;
  uint64_t notes;

public:
  explicit Clerk( const std::string& who )
    : name( who ), scratch( static_cast<unsigned char*>( malloc( ROOM ) ) ), notes( 0 )
  {}
  ~Clerk() { free( scratch ); }
  Clerk( const Clerk& ) = delete;
  Clerk& operator=( const Clerk& ) = delete;

  std::string who( void ) const { return name; }

  /* One more note, to at most ROOM; how many there are. */
  uint64_t note( void )
  {
    if ( notes < ROOM ) {
      notes = notes + 1;
    }
    return notes;
  }
};

}
