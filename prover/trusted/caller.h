/* Copyright 2026 Warren D. MacEvoy. MIT (strong-domain-driven-design, LICENSE): one of what the prover trusts, prover/trusted/. */

/*
 * Who called, and the end of the process.
 *
 * A way in for code that is not proved tests what it is given, when the program runs:
 *
 *     STRONG_CHECK( condition, from );
 *
 * If the condition is not so, the process ends there: it says which line called and what was
 * expected, and aborts. It is not an answer and not an exception: nothing can catch it, and
 * nothing goes on. So code that is not proved hands a way in only what it has itself made right;
 * what comes from anyone is first read by what is proved to read anything, or
 * tested by the code that hands it over. `from` is a Strong::caller, the last parameter of the
 * way in, with a default: the compiler fills it in with the line of whoever called.
 *
 * This file is the one thing under strong/ that is not proved: it writes to standard error and
 * ends the process, and that it does is trusted.
 */

#ifndef STRONG_CALLER_H
#define STRONG_CALLER_H

#include <cstdio>
#include <cstdlib>

namespace Strong {

struct caller
{
  const char* file;
  int line;
  caller( const char* f = __builtin_FILE(), int l = __builtin_LINE() ) : file( f ), line( l ) {}
};

[[noreturn]] inline void failed( const char* expected, caller from )
{
  fprintf( stderr, "%s:%d: called with what is not expected: %s\n", from.file, from.line, expected );
  abort();
}

}

#define STRONG_CHECK( condition, from )                                                                                \
  do {                                                                                                                 \
    if ( !( condition ) )                                                                                              \
      Strong::failed( #condition, from );                                                                              \
  } while ( 0 )

#endif
