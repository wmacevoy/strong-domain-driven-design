"""
one name   At a call of anything declared under SUBJECT, no two arguments taken by reference or
           by pointer name one thing, or one a part of the other, and none names the object the
           method is called on, or a part of it. So a method's parameters, and its object, are
           apart: what it writes by one is not seen by another. Refused otherwise, in code that
           is proved and in code that is not: so a part can be made strong without first being
           taken apart. At a call of what is declared elsewhere (the system's, INCLUDE's) such
           a pair is said, not refused, and only where one of the two may be written: a pair
           that is only read (`execl( shell, shell, ... )`, `v.find( k ) == v.end()`) is how
           those are called.

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
        self.unjudged = []
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
            elif strong and not fresh(g):
                self.unjudged.append("%s:%d: %s of %s is `%s`" % (rel, line, p.spelling or "a parameter", f.spelling, words(g)[:60]))
        for i in range(len(items)):
            for j in range(i + 1, len(items)):
                a, b = items[i], items[j]
                if not overlap(a[2], b[2]):
                    continue
                why = "%s and %s of %s are one thing, or one a part of the other" % (a[0], b[0], f.spelling)
                text = "%s:%d: %s:\n    %s" % (rel, line, why, line_at(c.location.file.name, line)[:150])
                if ours:
                    self.refused.append(text)
                elif "writes" in (a[1], b[1]):      # of the system's: said only where one of the two may be written
                    self.said.append(text)

    def found(self):
        """(refused, {name: lines said}), the lines as they are to be printed."""
        return self.refused, {"unjudged": sorted(set(self.unjudged)), "pairs": sorted(set(self.said))}
