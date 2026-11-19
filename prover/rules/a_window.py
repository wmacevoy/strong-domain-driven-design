"""
a window   A window (a class of STRONG's subarray.h: some elements, by where the first is and
           how many) expects that its elements are there and stay. So it does not outlive what
           it was made from: it is a local or a parameter, never a field, never a global or a
           static, never what a function gives back. And while one that has a name is in scope,
           what it was made from is not changed: not assigned to, not the object of a method
           that is not const, not handed to what may write it. Refused otherwise. Outside
           STRONG nothing of a window is called (it is made, and handed over), and each place
           one is made there is said: that its elements are there is that code's to keep.
"""
import os

import clang.cindex as ci
from clang.cindex import CursorKind as K, TypeKind as TK

from .names import callee, function_of, line_at, taken_by_name


class AWindow:
    def __init__(self, program):
        self.program = program
        self.refused = []
        self.made = []
        self.seen = set()

    def see_call(self, c):
        f = callee(c)
        if f is None:
            return
        program = self.program
        rel, line = program.at(c)
        if (program.under_strong(f) and os.path.basename(f.location.file.name) == "subarray.h"
                and not os.path.realpath(c.location.file.name).startswith(program.strong_dir)
                and not (f.kind == K.CONSTRUCTOR and (f.is_copy_constructor() or f.is_move_constructor()))):
            text = "%s:%d: %s" % (rel, line, line_at(c.location.file.name, line)[:150])
            if f.kind == K.CONSTRUCTOR:
                self.made.append(text)
            else:
                self.refused.append("%s:%d: outside %s/, %s is called of a window: there one is made, and handed over:\n    %s"
                                    % (rel, line, program.strong_name, f.spelling, line_at(c.location.file.name, line)[:150]))

    def see(self, c, path):
        if os.path.basename(path) == "subarray.h":
            return
        program = self.program
        window = program.window
        kept = None
        if c.kind == K.FIELD_DECL and window(c.type):
            kept = "a field"
        elif c.kind == K.VAR_DECL and window(c.type) and (c.storage_class == ci.StorageClass.STATIC
                                                          or c.semantic_parent.kind in (K.TRANSLATION_UNIT, K.NAMESPACE)):
            kept = "a global or a static"
        elif c.kind in (K.FUNCTION_DECL, K.CXX_METHOD) and window(c.result_type):
            kept = "what a function gives back"
        if c.kind == K.VAR_DECL and window(c.type) and not kept and c.type.get_canonical().kind == TK.RECORD \
                and c.semantic_parent.kind not in (K.TRANSLATION_UNIT, K.NAMESPACE) and (path, c.location.line, c.location.column, "held") not in self.seen:
            self.seen.add((path, c.location.line, c.location.column, "held"))
            self.held(c)
        if kept and (path, c.location.line, "kept") not in self.seen:
            self.seen.add((path, c.location.line, "kept"))
            rel, line = program.at(c)
            self.refused.append("%s:%d: a %s, a window on an array, is %s: it could outlive its array:\n    %s"
                                % (rel, line, window(c.type if kept != "what a function gives back" else c.result_type), kept, line_at(path, line)[:150]))

    def source_of(self, var):
        """What a window with a name was made from: the name its first argument begins at, or None."""
        def find(c):
            if c.kind == K.CALL_EXPR and c.referenced is not None and c.referenced.kind == K.CONSTRUCTOR:
                given = list(c.get_arguments())
                if given and self.program.window(c.type):
                    return self.program.name_of(given[0])
            for ch in c.get_children():
                r = find(ch)
                if r:
                    return r
            return None
        return find(var)

    def changes(self, c, root):
        """Why this expression may change the thing named `root`, or None."""
        name_of = self.program.name_of
        if c.kind == K.CALL_EXPR and c.referenced is not None and c.referenced.kind in (K.CXX_METHOD, K.FUNCTION_DECL, K.CONSTRUCTOR, K.FUNCTION_TEMPLATE):
            f = c.referenced
            params, given, ch = list(f.get_arguments()), list(c.get_arguments()), list(c.get_children())
            if f.kind == K.CXX_METHOD and not f.is_static_method() and not f.is_const_method():
                obj = None
                if len(given) == len(params) + 1:
                    obj, given = name_of(given[0]), given[1:]
                elif ch and ch[0].kind == K.MEMBER_REF_EXPR:
                    sub = list(ch[0].get_children())
                    obj = name_of(sub[0]) if sub else ("this", [])
                if obj and obj[0] == root:
                    return "%s, which is not const, is called on it" % f.spelling
            elif len(given) == len(params) + 1:
                given = given[1:]
            for p, g in zip(params, given):
                n = name_of(g)
                if n and n[0] == root and taken_by_name(p.type) == "writes":
                    return "it is handed to %s, which may write it" % f.spelling
        if c.kind in (K.BINARY_OPERATOR, K.COMPOUND_ASSIGNMENT_OPERATOR, K.UNARY_OPERATOR):
            ch = list(c.get_children())
            n = name_of(ch[0]) if ch else None
            if n and n[0] == root:
                if c.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
                    return "it is assigned to"
                ops = [t.spelling for t in c.get_tokens() if t.spelling in ("=", "++", "--")
                       and (c.kind == K.UNARY_OPERATOR or (ch[0].extent.end.offset <= t.extent.start.offset < ch[1].extent.start.offset))]
                if ops:
                    return "it is assigned to"
        return None

    def held(self, var):
        """A window with a name: what it was made from is not changed while it is in scope (here: for the rest of its function)."""
        fn, src = function_of(var), self.source_of(var)
        if fn is None or src is None:
            return
        def walk(c):
            if c.extent.start.offset > var.extent.end.offset:
                why = self.changes(c, src[0])
                if why:
                    rel, line = self.program.at(c)
                    self.refused.append("%s:%d: a window was made of this at line %d, and here %s: its elements may not be where they were:\n    %s"
                                        % (rel, line, var.location.line, why, line_at(c.location.file.name, line)[:150]))
            for ch in c.get_children():
                walk(ch)
        walk(fn)

    def found(self):
        return self.refused, {"made": sorted(set(self.made))}
