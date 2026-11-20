#!/usr/bin/env python3
"""
prooc -- a spike (2026-11-17): read a C++ class, refuse it if its boundary leaks, and write what
must be proven of it, for Lean.

It writes no C and nothing that ships.  For a class C in ordinary C++ it writes, into --out:

  CModel.lean   each method as a Lean function from the state and the arguments to the new state
                and the result, or `none` where the C++ would read or write outside an array; and
                the invariant, `Inv`, read from the class's own `bool invariant() const`
  COwed.lean    WHAT MUST BE PROVEN, as one statement, `C.Owed`: every method is safe (never `none`)
                from any state that satisfies the invariant, and leaves the invariant true.  It
                imports the model and nothing written by hand, so nothing written by hand can
                change what it says.  A proof of it is `C.Claims.owed` in CClaims.lean, written by a
                person or an agent, and trusted for nothing: Audit.lean checks it (see there)
  CDiff.lean, C_diff.cpp   the model and the C++ driven by the same numbers, to compare what they print

THE BOUNDARY.  A class is a domain only if nothing outside it can reach its state, so that an
invariant proved of its methods is an invariant of the program.  The generator refuses what would
let state out: a field that is not private, a friend, a base, a pointer or a reference anywhere,
`this` as a value, the address of anything.  And what it cannot give an exact meaning: see refuse().

Usage:  python3 prover/prooc.py prover/model/Gauge.hpp -o prover/gen
"""

import argparse
import os
import sys

import clang.cindex as ci

from clang_edge import configure_libclang, probe, Unsupported   # noqa: E402
from cxxtypes import OPTIONS, READ
import reader
from model import emit_model
from owed import emit_owed
from compare import (emit_diff_cpp, emit_diff_cpp_generic, emit_diff_lean, emit_diff_lean_generic,
                     emit_script)
from subject import PRE_FLAGS, file_scope, subject_text, with_pre


def main():
    ap = argparse.ArgumentParser(description="write what must be proven of a C++ class, for Lean")
    ap.add_argument("sources", nargs="+")
    ap.add_argument("--class", dest="klass", help="the one source is a file of another program: read this class of it, as it stands")
    ap.add_argument("--function", help="as --class, for a function that is not a method")
    ap.add_argument("--as", dest="as_name", help="with --class or --function: the name it is proved under, if not its own")
    ap.add_argument("--uses", action="append", default=[], metavar="FILE:CLASS",
                    help="with --class: a class its methods take as a parameter, read from its own file")
    ap.add_argument("--needs", action="append", default=[], metavar="FILE:NAME",
                    help="with --class: a name for a type or a number that it is written with, read from its own file")
    ap.add_argument("--invariant-may-be-absent", action="store_true",
                    help="a class with no `bool invariant() const` claims nothing of its state (for a class that cannot be changed)")
    ap.add_argument("-o", "--out", default="prover/gen")
    ap.add_argument("--std", default="c++20")
    ap.add_argument("--steps", type=int, default=2000)
    args = ap.parse_args()

    OPTIONS["no_invariant"] = args.invariant_may_be_absent
    configure_libclang()
    index = ci.Index.create()
    builtin = probe([os.environ.get("CC", "cc"), "-print-resource-dir"], "-resource-dir") \
        or probe([os.environ.get("CC", "cc"), "-print-file-name=include"], "-isystem")
    wanted = args.klass or args.function
    if wanted and (len(args.sources) != 1 or (args.klass and args.function)):
        raise Unsupported("--class or --function reads one thing of one file")
    written = []
    for path in args.sources:
        flags = ["-x", "c++", "-std=" + args.std, "-Wno-pragma-once-outside-header",
                 "-I" + os.path.dirname(os.path.abspath(path)),
                 "-I" + os.path.join(os.path.dirname(os.path.abspath(__file__)), "model")] + builtin
        qual = None
        if wanted:
            text, lines, qual = subject_text(index, path, wanted, args.std, builtin, function=bool(args.function),
                                             uses=[tuple(u.rsplit(":", 1)) for u in args.uses],
                                             needs=[tuple(u.rsplit(":", 1)) for u in args.needs])
            name = (args.as_name or wanted) + ".subject.hpp"
            said = "%s, %s" % (wanted, lines)
            here = os.path.abspath(os.path.join(args.out, name))
            written.append((name, text))
        else:
            name = said = os.path.basename(path)
            here = os.path.abspath(path)
            text = open(path, encoding="utf-8").read()
        read = with_pre(index, here, text, flags)
        header = name
        if read is not None:        # what is read, where a method says pre(...): beside the text itself
            header = name.rsplit(".", 2 if wanted else 1)[0] + ".read.hpp"
            written.append((header, read))
        READ["text"] = (read or text).encode("utf-8")
        tu = index.parse(here, args=flags + PRE_FLAGS, unsaved_files=[(here, read or text)])
        fatal = [d for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]
        if fatal:
            for d in fatal:
                print("prooc: %s" % d, file=sys.stderr)
            return 1
        classes = file_scope(tu.cursor, here, "function" if args.function else bool(args.klass))
        if not classes:
            raise Unsupported("%s: no class at file scope" % path)
        if wanted:          # the classes it uses stand before it in the text: they are read as parameters' types
            classes = [c for c in classes if c.spelling == wanted]
        for c in classes:
            k = reader.read(c)      # all that is refused is refused here: what follows writes
            k.qual = qual or k.name
            if wanted and args.as_name:
                k.name = args.as_name       # the Lean names and the files; the C++ is written with k.qual
            written += [(k.name + "Model.lean", emit_model(k, said)),
                        (k.name + "Owed.lean", emit_owed(k, said)),
                        (k.name + "Diff.lean", emit_diff_lean_generic(k) if k.generic else emit_diff_lean(k)),
                        (k.name + "_diff.cpp", emit_diff_cpp_generic(k, header) if k.generic else emit_diff_cpp(k, header)),
                        (k.name + ".script", emit_script(k, args.steps))]
    os.makedirs(args.out, exist_ok=True)       # everything is read before anything is written
    for name, text in written:
        open(os.path.join(args.out, name), "w").write(text)
        print("prooc: %s/%s" % (args.out, name))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Unsupported as e:
        print("prooc: refused\n  %s" % e, file=sys.stderr)
        sys.exit(2)
