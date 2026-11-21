"""
one name   At a call of anything declared under SUBJECT, what may be written by reference or
           by pointer has one name: no argument the call may write through (or the object of a
           method that is not const) is one thing with another argument or with the object, or
           a part of it. So what a method writes by one name is not seen by another. Arguments
           that are only read may be one thing (`same( data, data )`): nothing changes under
           either name. Refused otherwise, in code that is proved and in code that is not: so a
           part can be made strong without first being taken apart. At a call of what is proved,
           an argument that is not a name (a sum, a call's pointer result) cannot be judged, so
           beside anything the call may write it is refused: the caller hands a name, a copy
           where it may be the same (the client, 2026-11-21: "non-const alias are unique";
           "callers that cannot assure this should check and make copies as needed"). At a call
           of what is declared elsewhere (the system's, INCLUDE's) such a pair is said, not
           refused: `execl( shell, shell, ... )`, `v.find( k ) == v.end()` are how those are
           called.

It also counts the calls it looks at (calls, and of them proved_calls: of what is under STRONG),
which lint.py prints.
"""
import os

from clang.cindex import CursorKind as K

from .names import callee, fresh, line_at, overlap, taken_by_name, words


class OneName:
    def __init__(self, program):
        self.program = program
        self.refused = []
        self.said = []
        self.calls = 0
        self.proved_calls = 0

    def see_call(self, c):
        f = callee(c)
        if f is None:
            return
        program = self.program
        strong = program.under_strong(f) and os.path.basename(f.location.file.name) != "caller.h"
        ours = f.location.file is not None and os.path.realpath(f.location.file.name).startswith(program.subject_dir)
        self.calls += 1
        self.proved_calls += strong
        params, given, ch = list(f.get_arguments()), list(c.get_arguments()), list(c.get_children())
        items = []
        if f.kind == K.CXX_METHOD and not f.is_static_method():
            n = None
            if len(given) == len(params) + 1:                       # an operator: the object is written first
                n, given = program.name_of(given[0]), given[1:]
            elif ch and ch[0].kind == K.MEMBER_REF_EXPR:
                sub = list(ch[0].get_children())
                n = program.name_of(sub[0]) if sub else ("this", [])
            if n:
                items.append(("the object", "reads" if f.is_const_method() else "writes", n))
        rel, line = program.at(c)
        for p, g in zip(params, given):
            how = taken_by_name(p.type)
            if not how:
                continue
            n = program.name_of(g)
            if n:
                items.append(("`%s`" % (p.spelling or "a parameter"), how, n))
            elif strong and not fresh(g):                         # not a name: where it points is not judged
                items.append(("`%s` (`%s`, not a name)" % (p.spelling or "a parameter", words(g)[:60]), how, None))
        for i in range(len(items)):
            for j in range(i + 1, len(items)):
                a, b = items[i], items[j]
                if "writes" not in (a[1], b[1]):                  # both only read: one thing under two names changes nothing
                    continue
                if a[2] is None or b[2] is None:
                    why = "%s and %s of %s may be one thing, and one may be written: hand a name, a copy where it may be the same" % (a[0], b[0], f.spelling)
                elif overlap(a[2], b[2]):
                    why = "%s and %s of %s are one thing, or one a part of the other, and one may be written" % (a[0], b[0], f.spelling)
                else:
                    continue
                text = "%s:%d: %s:\n    %s" % (rel, line, why, line_at(c.location.file.name, line)[:150])
                if ours:
                    self.refused.append(text)
                else:
                    self.said.append(text)

    def found(self):
        """(refused, {name: lines said}), the lines as they are to be printed."""
        return self.refused, {"pairs": sorted(set(self.said))}
