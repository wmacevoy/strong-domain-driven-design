"""
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

Some of this is seen where it is written; the rest (what a function needs, carried to its callers;
what was kept) is settled in found(), when every file has been read.
"""
import os
import re

import clang.cindex as ci
from clang.cindex import CursorKind as K, TypeKind as TK

from .names import callee, function_of, inner, line_at, taken_by_name


def retain_file(cursor):
    f = cursor.location.file
    return f is not None and os.path.basename(f.name) == "retain.hpp"


def usr_of(f):
    """A function's name for the graph of calls: a template's own, for one made from it."""
    t = ci.conf.lib.clang_getSpecializedCursorTemplate(f)
    return (t if t is not None and t.kind != K.INVALID_FILE and t.get_usr() else f).get_usr()


def recalled(c):
    """('recall' or 'retained', T) for a call of retain.hpp's recall<T>() or retained<T>(); or None."""
    f = c.referenced if c.kind == K.CALL_EXPR else None
    if f is None or f.spelling not in ("recall", "retained") or not retain_file(f):
        return None
    t = f.result_type.get_canonical()
    if f.spelling == "recall" and t.kind == TK.LVALUEREFERENCE:
        return ("recall", t.get_pointee().get_pointee().get_canonical().spelling)
    return (f.spelling, f.get_template_argument_type(0).get_canonical().spelling)


def retains(t):
    """T, where this type is retain.hpp's retain<T>, or a class with one as a base; or None."""
    t = t.get_canonical()
    d = t.get_declaration()
    if d is None or d.kind not in (K.CLASS_DECL, K.STRUCT_DECL, K.CLASS_TEMPLATE):
        return None
    if d.spelling == "retain" and retain_file(d):
        m = re.match(r"(?:const )?retain<(.*)>$", t.spelling)
        return m.group(1).strip() if m else None
    for b in d.get_children():
        if b.kind == K.CXX_BASE_SPECIFIER:
            r = retains(b.type)
            if r:
                return r
    return None


def has(c, test):
    """Whether this expression, or anything in it, passes the test; and the callees in it."""
    found, callees = False, set()
    def walk(x):
        nonlocal found
        if test(x):
            found = True
        if x.kind == K.CALL_EXPR and x.referenced is not None:
            callees.add(usr_of(x.referenced))
        for ch in x.get_children():
            walk(ch)
    walk(c)
    return found, callees


def is_recall(x):
    r = recalled(x)
    return r is not None and r[0] == "recall"


class AContext:
    def __init__(self, program):
        self.program = program
        self.refused = []
        self.fn = []                            # the function being read (its usr), innermost last
        self.needs = {}                         # usr: {T: where}
        self.gives = {}                         # usr: {T: offset}
        self.callers = {}                       # callee usr: {(caller usr, offset)}
        self.names_of = {}                      # usr: (name, where)
        self.kept = []                          # candidates, settled when every file has been read
        self.handed = []
        self.gives_back = set()

    def keeps(self, c, what, rhs):
        """A pointer or a reference put where it outlasts the call: refused if what it is made from is what was recalled."""
        direct, callees = has(rhs, is_recall)
        rel, line = self.program.at(c)
        self.kept.append((direct, callees, "%s:%d: what was recalled is kept in %s: a context is the caller's, for the call and no longer:\n    %s"
                          % (rel, line, what, line_at(c.location.file.name, line)[:150])))

    def enter(self, c):
        """A function that is defined: what is seen until leave(c) is in it."""
        at = self.program.at
        self.fn.append(c.get_usr())
        self.names_of[c.get_usr()] = (c.spelling, "%s:%d" % at(c))
        if c.kind == K.CONSTRUCTOR:                 # a field made from what was recalled
            field = None
            for ch in c.get_children():
                if ch.kind == K.MEMBER_REF:
                    field = ch
                elif field is not None and ch.kind not in (K.COMPOUND_STMT, K.PARM_DECL):
                    if field.type.get_canonical().kind in (TK.POINTER, TK.LVALUEREFERENCE):
                        self.keeps(ch, "the field `%s`" % field.spelling, ch)
                    field = None

    def leave(self, c):
        self.fn.pop()

    def see_call(self, c):
        f = callee(c)
        if f is None:
            return
        program = self.program
        at = program.at
        if self.fn:
            self.callers.setdefault(usr_of(f), set()).add((self.fn[-1], c.extent.start.offset))
        r = recalled(c)
        if r:
            here = os.path.realpath(c.location.file.name)
            if here.startswith(program.strong_dir):
                self.refused.append("%s:%d: under %s/, a %s is asked for by %s: what is proved is handed what it needs:\n    %s"
                                    % (at(c)[0], at(c)[1], program.strong_name, r[1], r[0], line_at(here, c.location.line)[:150]))
            if r[0] == "recall" and self.fn:
                self.needs.setdefault(self.fn[-1], {}).setdefault(r[1], "%s:%d" % at(c))
        if f.spelling in ("begin", "end") and retain_file(f) and f.semantic_parent.spelling == "retain":
            self.refused.append("%s:%d: the frames above are walked (retain<T>::%s): a context is the nearest one retained, and no other:\n    %s"
                                % (at(c)[0], at(c)[1], f.spelling, line_at(c.location.file.name, c.location.line)[:150]))

    def see(self, c, path):
        """The rules of a context that are seen where it is written; the rest are settled in found()."""
        program = self.program
        at, name_of = program.at, program.name_of
        if c.kind in (K.VAR_DECL, K.FIELD_DECL) and retains(c.type) and c.type.get_canonical().kind == TK.RECORD:
            T = retains(c.type)
            rel, line = at(c)
            local = c.kind == K.VAR_DECL and c.storage_class != ci.StorageClass.STATIC and c.semantic_parent.kind not in (K.TRANSLATION_UNIT, K.NAMESPACE) \
                and c.semantic_parent.kind not in (K.CLASS_DECL, K.STRUCT_DECL, K.CLASS_TEMPLATE)
            if path.startswith(program.strong_dir):
                self.refused.append("%s:%d: under %s/, a %s is retained: what is proved is handed what it needs, and hands on what it is handed:\n    %s"
                                    % (rel, line, program.strong_name, T, line_at(path, line)[:150]))
            elif not local:
                self.refused.append("%s:%d: a retain of %s that is not a local: a context is a frame's, and ends with it:\n    %s" % (rel, line, T, line_at(path, line)[:150]))
            elif self.fn:
                self.gives.setdefault(self.fn[-1], {}).setdefault(T, c.extent.end.offset)
                src = None                                   # what is retained: `retain<T> as( &thing );`
                for ch in c.get_children():
                    if ch.kind == K.CALL_EXPR and ch.referenced is not None and ch.referenced.kind == K.CONSTRUCTOR:
                        given = list(ch.get_arguments())
                        src = name_of(given[0]) if given else None
                fn = function_of(c)
                if src and fn is not None:
                    def walk(x):
                        if x.kind == K.CALL_EXPR and x.referenced is not None and x.extent.start.offset > c.extent.end.offset \
                                and x.referenced.kind in (K.FUNCTION_DECL, K.CXX_METHOD, K.FUNCTION_TEMPLATE):
                            params, given = list(x.referenced.get_arguments()), list(x.get_arguments())
                            if len(given) == len(params) + 1:
                                given = given[1:]
                            for p, g in zip(params, given):
                                n = name_of(g)
                                if n and n[0] == src[0] and taken_by_name(p.type):
                                    r2, l2 = at(x)
                                    self.handed.append((usr_of(x.referenced), T, "%s:%d: what is retained as the %s is also handed to %s, which needs one retained: one thing, two names:\n    %s"
                                                        % (r2, l2, T, x.referenced.spelling, line_at(x.location.file.name, l2)[:150])))
                        for ch in x.get_children():
                            walk(ch)
                    walk(fn)
        if c.kind == K.VAR_DECL and "retain<" in c.type.get_canonical().spelling and "iterator" in c.type.get_canonical().spelling:
            self.refused.append("%s:%d: the frames above are walked (an iterator of retain<T>): a context is the nearest one retained, and no other:\n    %s"
                                % (at(c)[0], at(c)[1], line_at(path, c.location.line)[:150]))
        if c.kind == K.VAR_DECL and c.type.get_canonical().kind in (TK.POINTER, TK.LVALUEREFERENCE) and (
                c.storage_class == ci.StorageClass.STATIC or c.semantic_parent.kind in (K.TRANSLATION_UNIT, K.NAMESPACE)):
            self.keeps(c, "`%s`, a global or a static" % c.spelling, c)
        if c.kind == K.BINARY_OPERATOR:
            ch = list(c.get_children())
            if len(ch) == 2 and any(t.spelling == "=" and ch[0].extent.end.offset <= t.extent.start.offset < ch[1].extent.start.offset for t in c.get_tokens()):
                if is_recall(inner(ch[0])):
                    self.refused.append("%s:%d: what is recalled is pointed elsewhere: a context is the caller's to set, by retaining:\n    %s"
                                        % (at(c)[0], at(c)[1], line_at(path, c.location.line)[:150]))
                n = name_of(ch[0])
                if n and ch[0].type.get_canonical().kind == TK.POINTER and (n[0] == "this" or "@F@" not in n[0]):
                    self.keeps(c, "a field or a global", ch[1])
        if c.kind == K.RETURN_STMT and self.fn and has(c, is_recall)[0]:
            self.gives_back.add(self.fn[-1])

    def found(self):
        """What each function needs retained is carried to its callers until one retains it first."""
        refused = list(self.refused)
        need = {(fn, T) for fn, ts in self.needs.items() for T in ts}
        work = list(need)
        while work:
            fn, T = work.pop()
            for caller, offset in self.callers.get(fn, ()):
                given = self.gives.get(caller, {}).get(T)
                if given is not None and offset > given:
                    continue
                if (caller, T) not in need:
                    need.add((caller, T))
                    work.append((caller, T))
        outside = []
        for fn, T in sorted(need):
            if not self.callers.get(fn):
                name, where = self.names_of.get(fn, ("?", "?"))
                if name == "main":
                    refused.append("%s: main needs a %s retained before what it calls, and nothing above main can retain one" % (where, T))
                else:
                    outside.append("%s: %s needs a %s retained" % (where, name, T))
        for direct, callees, text in self.kept:
            if direct or callees & self.gives_back:
                refused.append(text)
        for callee_usr, T, text in self.handed:
            if (callee_usr, T) in need:
                refused.append(text)
        return refused, {"outside": outside}
