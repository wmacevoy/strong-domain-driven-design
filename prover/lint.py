#!/usr/bin/env python3
"""
lint -- what a proof takes as given of the program around it, looked for in the program.

A class is proved alone: its methods, one at a time, each from a state that keeps the invariant.
That is the whole of what is owed only if the rest of the program lets it be: if nothing else
reaches the object's bytes, if what a method is handed is not also something else it is handed,
and if nothing else runs while it does. A proof cannot say these; they are of the program, not of
the class. This looks for each, in every file, before anything is proved:

    SUBJECT=dir STRONG=rel [INCLUDE=dir:dir...] [STD=gnu++20] python3 lint.py

SUBJECT is the program's directory, STRONG the directory under it where what is proved stands
(ingress.py holds that to be so), INCLUDE where else its `#include`s are found.

  one name   At a call of anything declared under SUBJECT, what may be written by reference or
             by pointer has one name: no argument the call may write through (or the object of
             a method that is not const) is one thing with another argument or the object, or a
             part of it. Arguments only read may be one thing. At a call of what is proved, an
             argument that is not a name, beside anything the call may write, is refused: the
             caller hands a name, a copy where it may be the same. Refused in code that is proved
             and in code that is not; at a call of the system's (INCLUDE's), said, not refused.
  one owner  An object is used by one thread at a time, and objects apart by as many threads as
             is useful. That holds if no two objects share state that is written: so there is no
             global, no static in a function and no static member that can be written, but one
             that is each thread's own (`thread_local`) or made for many threads (`std::atomic`).
             Refused of what is under STRONG. Of anything else each one is said; and where there
             is one, starting a thread (std::thread, std::jthread, std::async, pthread_create)
             is refused. Where a thread is started and there is none, each start is said: that
             what it is handed is its alone is read by a person. A signal handler that is a
             function is said, each one: it runs between any two steps of its thread.
  own bytes  Outside STRONG, a value of a class declared under STRONG is reached by its methods
             and by copying it whole, and no other way: its address is not taken, a pointer or
             reference to it is not cast, and it is not a member of a union. So its fields are
             changed by its own methods and by nothing else. Refused otherwise.

  a window   A window (a class of STRONG's subarray.h: some elements, by where the first is and
             how many) expects that its elements are there and stay. So it does not outlive what
             it was made from: it is a local or a parameter, never a field, never a global or a
             static, never what a function gives back. And while one that has a name is in scope,
             what it was made from is not changed: not assigned to, not the object of a method
             that is not const, not handed to what may write it. Refused otherwise. Outside
             STRONG nothing of a window is called (it is made, and handed over), and each place
             one is made there is said: that its elements are there is that code's to keep.
  nothing    No method gives back a pointer or a reference to its own object's state, or a view
  leaves     or an iterator into it: what a class keeps is reached through its methods, while
             they run, and not after. Refused of a class under STRONG; said, each one, of any
             other class (`return *this;` is not one: the caller had the object already).
  a context  What a function needs and is not handed (retain.hpp: `retain<T> as( &thing );` in a
             frame, `recall<T>()` in what that frame calls) is a parameter that is not written.
             So a function that recalls a T needs one retained, and so does whatever calls it,
             up to a function that retains one before the call. `main` is refused if the need
             reaches it. A function it reaches that nothing of this program calls is said: it is
             entered from outside (a callback, a hook), and that a T is retained there is that
             caller's to keep. And a context stays what a parameter is: a retain is a local,
             never a field, a global or a static; what is recalled is not kept (no pointer or
             reference to it in a field, a global or a static), not pointed elsewhere
             (`recall<T>() = ...`), and the other frames' are not walked (`retain<T>::begin()`);
             what is retained is not also handed by reference to what recalls it (one thing, two
             names); and nothing under STRONG retains or recalls: what is proved is handed what
             it needs. Refused otherwise.
  a domain   With DOMAINS (a map, rules/a_domain.py says its form): another domain is used only
             by what its ABI headers declare, and included only by them; an ABI header names no
             type of its own domain's inside; every file is of one domain. Refused otherwise.

It reads what is written at the call (SE1/U4, chosen), by Clang's library. So it does not see
  - one thing reached by two names (two pointers that were made equal somewhere else);
  - an argument that is not a name (a sum, a call's pointer result): at a call of what is proved,
    beside anything the call may write, it is refused; the caller hands a name;
  - bytes written over a struct that has a proved value in it (memset of the struct whole);
  - a reference into a container that is then made to grow (but for a window with a name);
  - a window made from a pointer: what the pointer points into is not followed;
  - state that leaves by a local reference, or by a parameter that is written through;
  - a call through a pointer to a function, a `std::function` or a virtual method: what it needs retained is not followed.
A file it cannot read whole is refused, and named: nothing is said of what was not read.
Exit 1 if anything is refused.
"""
import os
import sys

import clang.cindex as ci
from clang.cindex import CursorKind as K

from clang_edge import configure_libclang, probe   # noqa: E402
from rules.a_context import AContext
from rules.a_domain import ADomain
from rules.a_window import AWindow
from rules.names import CASTS, FUNCTIONS, Program, plain
from rules.nothing_leaves import NothingLeaves
from rules.one_name import OneName
from rules.one_owner import OneOwner
from rules.own_bytes import OwnBytes

SOURCES = (".cc", ".cpp")
HEADERS = (".h", ".hpp")
ONCE = (K.CALL_EXPR, K.UNARY_OPERATOR, K.UNION_DECL) + CASTS      # kinds a header parsed twice shows twice

# What is said, in the order it is printed: (name a rule gives it, title).
SAID = (("made", "window%s made by code that is not proved (that its elements are there, and stay, is that code's to keep)"),
        ("leaves", "method%s of a class that is not proved that give back what is of their own object"),
        ("pairs", "pair%s of arguments that are one thing, in calls of what is not this program's"),
        ("shared", "thing%s that can be written and shared by every object and thread (so no thread may be started)"),
        ("outside", "function%s nothing of this program calls that need a context retained (each is entered from outside: that one is retained there is assumed)"),
        ("threads", "thread%s started (that what each is handed is its alone is read by a person)"),
        ("handlers", "signal handler%s (each runs between any two steps: that it touches nothing proved is read by a person)"),
        ("crossings", "crossing%s into another domain's inside that the map allows until it goes (DOMAINS: allow)"))


class Walk:
    """One walk of a tree: each cursor goes to each rule that sees cursors, each call to each that sees calls."""

    def __init__(self, program, seeing, calling, scoped):
        self.program = program
        self.seeing = seeing            # rules with see( cursor, path )
        self.calling = calling          # rules with see_call( cursor )
        self.scoped = scoped            # rules with enter( function ) and leave( function )
        self.seen = set()               # so that a header parsed twice is judged once

    def visit(self, c):
        f = c.location.file
        entered = False
        if f is not None:
            path = os.path.realpath(f.name)
            if not path.startswith(self.program.subject_dir):
                return                                              # the system's, and INCLUDE's: not this program
            if c.kind in ONCE:
                key = (path, c.location.line, c.location.column, c.extent.end.offset, c.kind.value)      # (a call in a call begins where it does)
                if key in self.seen:
                    return
                self.seen.add(key)
            if c.kind == K.CALL_EXPR:
                for rule in self.calling:
                    rule.see_call(c)
            if c.kind in FUNCTIONS and c.is_definition():
                for rule in self.scoped:
                    rule.enter(c)
                entered = True
            for rule in self.seeing:
                rule.see(c, path)
        for ch in c.get_children():
            self.visit(ch)
        if entered:
            for rule in self.scoped:
                rule.leave(c)


def main():
    subject, strong = os.environ.get("SUBJECT"), os.environ.get("STRONG")
    if not subject or not strong:
        sys.exit("lint: set SUBJECT, and STRONG (the directory under it where what is proved stands)")
    program = Program(subject, strong)

    one_name, one_owner, own_bytes = OneName(program), OneOwner(program), OwnBytes(program)
    a_window, nothing_leaves, a_context = AWindow(program), NothingLeaves(program), AContext(program)
    rules = [one_name, one_owner, a_window, nothing_leaves, own_bytes, a_context]
    seeing = [one_owner, a_window, nothing_leaves, own_bytes, a_context]
    a_domain = None
    if os.environ.get("DOMAINS"):
        a_domain = ADomain(program, os.path.join(program.subject, os.environ["DOMAINS"]))
        rules.append(a_domain)
        seeing.append(a_domain)
    walk = Walk(program, seeing=seeing, calling=[one_name, a_window, a_context], scoped=[a_context])

    configure_libclang()
    index = ci.Index.create()
    builtin = probe([os.environ.get("CC", "cc"), "-print-resource-dir"], "-resource-dir") \
        or probe([os.environ.get("CC", "cc"), "-print-file-name=include"], "-isystem")
    flags = ["-x", "c++", "-std=" + os.environ.get("STD", "gnu++20"), "-Wno-everything", "-I" + program.subject]
    flags += ["-I" + d for d in os.environ.get("INCLUDE", "").split(":") if d] + builtin

    # one owner: threads and signal handlers by the words, in every file
    files = []
    for root, _, names in sorted(os.walk(program.subject)):
        for f in sorted(names):
            if f.endswith(SOURCES + HEADERS):
                path = os.path.realpath(os.path.join(root, f))
                files.append(path)
                one_owner.see_text(path, plain(open(path, encoding="utf-8", errors="replace").read()))

    # by Clang's reading. Each source, then each header no source brought in.
    unread, reached = [], set()
    for path in [p for p in files if p.endswith(SOURCES)] + [p for p in files if p.endswith(HEADERS)]:
        if path in reached:
            continue
        tu = index.parse(path, args=flags)
        errors = [d for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]
        if errors:
            unread.append("%s: %s" % (os.path.relpath(path, program.subject), errors[0].spelling))
        reached.add(path)
        for inc in tu.get_includes():
            reached.add(os.path.realpath(inc.include.name))
        walk.visit(tu.cursor)

    if a_domain is not None:
        a_domain.check_files(files, [d for d in os.environ.get("INCLUDE", "").split(":") if d])
    refused, said = [], {}
    for rule in rules:
        r, s = rule.found()
        refused += r
        said.update(s)

    for r in unread:
        print("lint: could not be read whole (set INCLUDE to where its #includes are): %s" % r)
    for r in sorted(set(refused)):
        print("lint: " + r)
    if unread or refused:
        print("lint: REFUSED: %d. What is proved is proved alone; this is what lets it be." % (len(unread) + len(set(refused))))
        sys.exit(1)
    print("lint: ok: %d files, %d calls, %d of them of what is under %s/: what a call may write has no second name at it, "
          "no thread is started beside state all share, and nothing outside reaches a proved value's bytes"
          % (len(files), one_name.calls, one_name.proved_calls, program.strong_name))
    for name, title in SAID:
        lines = said.get(name, [])
        if lines:
            print("lint: %d %s:" % (len(lines), title % ("" if len(lines) == 1 else "s")))
            for x in lines:
                print("    " + x.replace("\n    ", "  |  ")[:200])


if __name__ == "__main__":
    main()
