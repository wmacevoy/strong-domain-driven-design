/*
  prover sample: what a method gives back, of a class the prover does not read (a Note: a mark and
  a std::string). Ordinary C++; nothing here knows the tool.
*/
#pragma once
#include "made/mark.h"
#include <string>

class Note {
public:
  const Mark mark;
  const std::string text;

  Note( const Mark& m, const std::string& t ) : mark( m ), text( t ) {}
};
