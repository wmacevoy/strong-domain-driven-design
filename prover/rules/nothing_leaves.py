"""
nothing    No method gives back a pointer or a reference to its own object's state, or a view
leaves     or an iterator into it: what a class keeps is reached through its methods, while
           they run, and not after. Refused of a class under STRONG; said, each one, of any
           other class (`return *this;` is not one: the caller had the object already).
"""
import os

import clang.cindex as ci
from clang.cindex import CursorKind as K, TypeKind as TK

from .names import NOT_EXPRESSION, inner, line_at

VIEWS = ("string_view", "iterator", "span<")


class NothingLeaves:
    def __init__(self, program):
        self.program = program
        self.refused = []
        self.leaves = []
        self.seen = set()

    def see(self, c, path):
        if os.path.basename(path) == "subarray.h":
            return
        if c.kind == K.CXX_METHOD and c.is_definition() and (path, c.location.line, c.location.column, "leaves") not in self.seen:
            self.seen.add((path, c.location.line, c.location.column, "leaves"))
            self.leaving(c)

    def leaving(self, method):
        """A public method that gives back a pointer, a reference, a view or an iterator: does it name its own object's
        state? A local it gives back is followed to what it was made from, and to what was assigned to it."""
        program = self.program
        t = method.result_type.get_canonical()
        if t.kind not in (TK.POINTER, TK.LVALUEREFERENCE) and not any(v in method.result_type.spelling or v in t.spelling for v in VIEWS):
            return
        if method.access_specifier not in (ci.AccessSpecifier.PUBLIC, ci.AccessSpecifier.INVALID):
            return                      # of the class's own inside: it does not leave by this
        given = {}                      # a local: every expression it is made from or assigned
        def gather(c):
            if c.kind == K.VAR_DECL:
                for e in c.get_children():
                    if e.kind not in NOT_EXPRESSION:
                        given.setdefault(c.get_usr(), []).append(e)
            if c.kind == K.BINARY_OPERATOR:
                ch = list(c.get_children())
                lhs = inner(ch[0]) if len(ch) == 2 else None
                if lhs is not None and lhs.kind == K.DECL_REF_EXPR and lhs.referenced is not None and lhs.referenced.kind == K.VAR_DECL:
                    given.setdefault(lhs.referenced.get_usr(), []).append(ch[1])
            for ch in c.get_children():
                gather(ch)
        gather(method)
        def own(e, depth=0):
            n = program.name_of(e)
            if n is None:
                return None
            if n[0] == "this":
                return ".".join(n[1]) if n[1] else None
            if depth < 4:
                for g in given.get(n[0], []):
                    r = own(g, depth + 1)
                    if r:
                        return r
            return None
        def walk(c):
            if c.kind == K.LAMBDA_EXPR:
                return
            if c.kind == K.RETURN_STMT:
                for e in c.get_children():
                    what = own(e)
                    if what:
                        rel, line = program.at(c)
                        text = "%s:%d: %s gives back what is of its own object (%s): it could be read, or changed, after the method has ended:\n    %s" % (
                            rel, line, method.spelling, what, line_at(c.location.file.name, line)[:150])
                        (self.refused if program.under_strong(method) else self.leaves).append(text)
            for ch in c.get_children():
                walk(ch)
        walk(method)

    def found(self):
        return self.refused, {"leaves": sorted(set(self.leaves))}
