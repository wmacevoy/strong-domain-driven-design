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

  one name   At a call of anything declared under SUBJECT, no two arguments taken by reference or
             by pointer name one thing, or one a part of the other, and none names the object the
             method is called on, or a part of it. So a method's parameters, and its object, are
             apart: what it writes by one is not seen by another. Refused otherwise, in code that
             is proved and in code that is not: so a part can be made strong without first being
             taken apart. At a call of what is declared elsewhere (the system's, INCLUDE's) such
             a pair is said, not refused, and only where one of the two may be written: a pair
             that is only read (`execl( shell, shell, ... )`, `v.find( k ) == v.end()`) is how
             those are called.
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

It reads what is written at the call (SE1/U4, chosen), by Clang's library. So it does not see
  - one thing reached by two names (two pointers that were made equal somewhere else);
  - an argument that is not a name (a sum, a call's pointer result): each is said, "not judged";
  - bytes written over a struct that has a proved value in it (memset of the struct whole);
  - a reference into a container that is then made to grow (but for a window with a name);
  - a window made from a pointer: what the pointer points into is not followed;
  - state that leaves by a local reference, or by a parameter that is written through.
A file it cannot read whole is refused, and named: nothing is said of what was not read.
Exit 1 if anything is refused.
"""
import os
import re
import sys

import clang.cindex as ci
from clang.cindex import CursorKind as K, TypeKind as TK

from oopcc import configure_libclang, probe   # noqa: E402

SUBJECT = os.environ.get("SUBJECT")
STRONG = os.environ.get("STRONG")
if not SUBJECT or not STRONG:
    sys.exit("lint: set SUBJECT, and STRONG (the directory under it where what is proved stands)")
SUBJECT = os.path.realpath(SUBJECT)
STRONG_DIR = os.path.join(SUBJECT, STRONG.strip("/")) + os.sep
SOURCES = (".cc", ".cpp")
HEADERS = (".h", ".hpp")

SKIP = (K.UNEXPOSED_EXPR, K.PAREN_EXPR, K.CXX_STATIC_CAST_EXPR, K.CXX_REINTERPRET_CAST_EXPR,
        K.CXX_CONST_CAST_EXPR, K.CSTYLE_CAST_EXPR, K.CXX_FUNCTIONAL_CAST_EXPR)
CASTS = (K.CXX_REINTERPRET_CAST_EXPR, K.CXX_CONST_CAST_EXPR, K.CSTYLE_CAST_EXPR, K.CXX_STATIC_CAST_EXPR)
THREADS = r"\bstd\s*::\s*(?:thread|jthread|async)\b|\bpthread_create\b"


def plain(text):
    """The text with comments and what is in quotes made blank, no line moved."""
    def blank(m):
        return re.sub(r"[^\n]", " ", m.group(0))
    return re.sub(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\\n])*"|\'(?:\\.|[^\'\\\n])*\'', blank, text, flags=re.S)


def inner(e):
    """The expression inside brackets, casts and what the compiler wrote around it."""
    while e.kind in SKIP:
        ch = [c for c in e.get_children() if c.kind not in (K.TYPE_REF, K.NAMESPACE_REF, K.TEMPLATE_REF)]
        if len(ch) != 1:
            return e
        e = ch[0]
    return e


def words(e):
    return " ".join(t.spelling for t in e.get_tokens())


def name_of(e):
    """(what it begins at, [the steps from there]) for an expression that names a thing; or None."""
    e = inner(e)
    if e.kind == K.DECL_REF_EXPR:
        d = e.referenced
        if d is None or d.kind in (K.FUNCTION_DECL, K.CXX_METHOD, K.ENUM_CONSTANT_DECL):
            return None
        return (d.get_usr() or d.spelling, [])
    if e.kind == K.CXX_THIS_EXPR:
        return ("this", [])
    if e.kind == K.MEMBER_REF_EXPR:
        d = e.referenced
        if d is None or d.kind != K.FIELD_DECL:
            return None
        ch = list(e.get_children())
        base = name_of(ch[0]) if ch else ("this", [])
        return None if base is None else (base[0], base[1] + [d.spelling])
    if e.kind == K.UNARY_OPERATOR:
        ch = list(e.get_children())
        first = next(iter(e.get_tokens()), None)
        if first is not None and first.spelling in ("&", "*") and len(ch) == 1:
            return name_of(ch[0])
        return None
    if e.kind == K.BINARY_OPERATOR:            # a pointer and a number: still in what the pointer is in
        ch = list(e.get_children())
        if len(ch) == 2 and e.type.get_canonical().kind == TK.POINTER:
            return name_of(ch[0]) or name_of(ch[1])
        return None
    if e.kind == K.ARRAY_SUBSCRIPT_EXPR:
        ch = list(e.get_children())
        base = name_of(ch[0])
        return None if base is None else (base[0], base[1] + ["[" + words(ch[1]) + "]"])
    if e.kind == K.CALL_EXPR and e.referenced is not None:
        n = e.referenced.spelling
        given, ch = list(e.get_arguments()), list(e.get_children())
        if n == "operator[]" and len(given) == 2:
            base = name_of(given[0])
            return None if base is None else (base[0], base[1] + ["[" + words(given[1]) + "]"])
        if n in ("operator->", "operator*") and len(given) == 1:
            return name_of(given[0])
        if n in ("c_str", "data", "front", "back", "begin", "end", "find", "at", "rbegin", "lower_bound", "upper_bound") and ch and ch[0].kind == K.MEMBER_REF_EXPR \
                and not (e.referenced.location.file and os.path.realpath(e.referenced.location.file.name).startswith(SUBJECT + os.sep)):
            sub = list(ch[0].get_children())       # the bytes a string or a vector keeps: some part of it
            base = name_of(sub[0]) if sub else ("this", [])
            return None if base is None else (base[0], base[1] + ["*"])
    return None


def fresh(e):
    """An argument that can be no one else's: a literal, or a value just made."""
    e = inner(e)
    if e.kind in (K.STRING_LITERAL, K.INTEGER_LITERAL, K.CXX_NULL_PTR_LITERAL_EXPR, K.GNU_NULL_EXPR,
                  K.CXX_BOOL_LITERAL_EXPR, K.CHARACTER_LITERAL, K.FLOATING_LITERAL):
        return True
    if e.kind == K.CALL_EXPR:
        return e.type.get_canonical().kind not in (TK.POINTER, TK.LVALUEREFERENCE, TK.RVALUEREFERENCE)
    return False


def taken_by_name(t):
    """'writes' or 'reads' for a parameter that is a reference or a pointer; None for a value."""
    t = t.get_canonical()
    if t.kind in (TK.LVALUEREFERENCE, TK.POINTER):
        p = t.get_pointee()
        if p.kind in (TK.FUNCTIONPROTO, TK.FUNCTIONNOPROTO):
            return None
        return "reads" if p.is_const_qualified() else "writes"
    return None


def overlap(a, b):
    if a[0] != b[0]:
        return False
    return all(x == y or "*" in (x, y) for x, y in zip(a[1], b[1]))


def under_strong(cursor):
    f = cursor.location.file
    return f is not None and os.path.realpath(f.name).startswith(STRONG_DIR)


def proved_record(t):
    """The class declared under STRONG that this type is, or points or refers to; or None."""
    t = t.get_canonical()
    while t.kind in (TK.POINTER, TK.LVALUEREFERENCE, TK.RVALUEREFERENCE, TK.CONSTANTARRAY, TK.INCOMPLETEARRAY):
        t = t.get_pointee() if t.kind in (TK.POINTER, TK.LVALUEREFERENCE, TK.RVALUEREFERENCE) else t.element_type
        t = t.get_canonical()
    d = t.get_declaration()
    if d is None or d.kind not in (K.CLASS_DECL, K.STRUCT_DECL, K.CLASS_TEMPLATE) or not under_strong(d):
        return None
    if os.path.basename(d.location.file.name) == "caller.h":      # who called: not proved, and nothing kept
        return None
    return d.spelling


def window(t):
    """The class of STRONG's subarray.h that this type is, or points or refers to, or is an array of; or None."""
    t = t.get_canonical()
    while t.kind in (TK.POINTER, TK.LVALUEREFERENCE, TK.RVALUEREFERENCE, TK.CONSTANTARRAY, TK.INCOMPLETEARRAY):
        t = t.get_pointee() if t.kind in (TK.POINTER, TK.LVALUEREFERENCE, TK.RVALUEREFERENCE) else t.element_type
        t = t.get_canonical()
    d = t.get_declaration()
    if d is None or d.location.file is None or not under_strong(d) or os.path.basename(d.location.file.name) != "subarray.h":
        return None
    return d.spelling


seen = set()
refused, said, unjudged, made, leaves, shared = [], [], [], [], [], []
VIEWS = ("string_view", "iterator", "span<")
calls = [0, 0]      # all; of what is proved


def line_at(path, n):
    try:
        return open(path, encoding="utf-8", errors="replace").read().split("\n")[n - 1].strip()
    except OSError:
        return ""


def at(c):
    return os.path.relpath(os.path.realpath(c.location.file.name), SUBJECT), c.location.line


def call(c):
    f = c.referenced
    if f is None or f.kind not in (K.FUNCTION_DECL, K.CXX_METHOD, K.CONSTRUCTOR, K.FUNCTION_TEMPLATE):
        return
    strong = under_strong(f) and os.path.basename(f.location.file.name) != "caller.h"
    ours = f.location.file is not None and os.path.realpath(f.location.file.name).startswith(SUBJECT + os.sep)
    calls[0] += 1
    calls[1] += strong
    params, given, ch = list(f.get_arguments()), list(c.get_arguments()), list(c.get_children())
    items = []
    if f.kind == K.CXX_METHOD and not f.is_static_method():
        n = None
        if len(given) == len(params) + 1:                       # an operator: the object is written first
            n, given = name_of(given[0]), given[1:]
        elif ch and ch[0].kind == K.MEMBER_REF_EXPR:
            sub = list(ch[0].get_children())
            n = name_of(sub[0]) if sub else ("this", [])
        if True:
            if n:
                items.append(("the object", "reads" if f.is_const_method() else "writes", n))
    rel, line = at(c)
    if (under_strong(f) and os.path.basename(f.location.file.name) == "subarray.h"
            and not os.path.realpath(c.location.file.name).startswith(STRONG_DIR)
            and not (f.kind == K.CONSTRUCTOR and (f.is_copy_constructor() or f.is_move_constructor()))):
        text = "%s:%d: %s" % (rel, line, line_at(c.location.file.name, line)[:150])
        if f.kind == K.CONSTRUCTOR:
            made.append(text)
        else:
            refused.append("%s:%d: outside %s/, %s is called of a window: there one is made, and handed over:\n    %s"
                           % (rel, line, STRONG.strip("/"), f.spelling, line_at(c.location.file.name, line)[:150]))
    for p, g in zip(params, given):
        how = taken_by_name(p.type)
        if not how:
            continue
        n = name_of(g)
        if n:
            items.append(("`%s`" % (p.spelling or "a parameter"), how, n))
        elif strong and not fresh(g):
            unjudged.append("%s:%d: %s of %s is `%s`" % (rel, line, p.spelling or "a parameter", f.spelling, words(g)[:60]))
    for i in range(len(items)):
        for j in range(i + 1, len(items)):
            a, b = items[i], items[j]
            if not overlap(a[2], b[2]):
                continue
            why = "%s and %s of %s are one thing, or one a part of the other" % (a[0], b[0], f.spelling)
            text = "%s:%d: %s:\n    %s" % (rel, line, why, line_at(c.location.file.name, line)[:150])
            if ours:
                refused.append(text)
            elif "writes" in (a[1], b[1]):      # of the system's: said only where one of the two may be written
                said.append(text)


def function_of(c):
    p = c.semantic_parent
    while p is not None and p.kind not in (K.FUNCTION_DECL, K.CXX_METHOD, K.CONSTRUCTOR, K.DESTRUCTOR, K.FUNCTION_TEMPLATE, K.TRANSLATION_UNIT):
        p = p.semantic_parent
    return p if p is not None and p.kind != K.TRANSLATION_UNIT else None


def source_of(var):
    """What a window with a name was made from: the name its first argument begins at, or None."""
    def find(c):
        if c.kind == K.CALL_EXPR and c.referenced is not None and c.referenced.kind == K.CONSTRUCTOR:
            given = list(c.get_arguments())
            if given and window(c.type):
                return name_of(given[0])
        for ch in c.get_children():
            r = find(ch)
            if r:
                return r
        return None
    return find(var)


def changes(c, root):
    """Why this expression may change the thing named `root`, or None."""
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


def held(var):
    """A window with a name: what it was made from is not changed while it is in scope (here: for the rest of its function)."""
    fn, src = function_of(var), source_of(var)
    if fn is None or src is None:
        return
    def walk(c):
        if c.extent.start.offset > var.extent.end.offset:
            why = changes(c, src[0])
            if why:
                rel, line = at(c)
                refused.append("%s:%d: a window was made of this at line %d, and here %s: its elements may not be where they were:\n    %s"
                               % (rel, line, var.location.line, why, line_at(c.location.file.name, line)[:150]))
        for ch in c.get_children():
            walk(ch)
    walk(fn)


def leaving(method):
    """A public method that gives back a pointer, a reference, a view or an iterator: does it name its own object's
    state? A local it gives back is followed to what it was made from, and to what was assigned to it."""
    t = method.result_type.get_canonical()
    if t.kind not in (TK.POINTER, TK.LVALUEREFERENCE) and not any(v in method.result_type.spelling or v in t.spelling for v in VIEWS):
        return
    if method.access_specifier not in (ci.AccessSpecifier.PUBLIC, ci.AccessSpecifier.INVALID):
        return                      # of the class's own inside: it does not leave by this
    given = {}                      # a local: every expression it is made from or assigned
    def gather(c):
        if c.kind == K.VAR_DECL:
            for e in c.get_children():
                if e.kind not in (K.TYPE_REF, K.NAMESPACE_REF, K.TEMPLATE_REF):
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
        n = name_of(e)
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
                    rel, line = at(c)
                    text = "%s:%d: %s gives back what is of its own object (%s): it could be read, or changed, after the method has ended:\n    %s" % (
                        rel, line, method.spelling, what, line_at(c.location.file.name, line)[:150])
                    (refused if under_strong(method) else leaves).append(text)
        for ch in c.get_children():
            walk(ch)
    walk(method)


def visit(c):
    f = c.location.file
    if f is not None:
        path = os.path.realpath(f.name)
        if not path.startswith(SUBJECT + os.sep):
            return                                              # the system's, and INCLUDE's: not this program
        key = (path, c.location.line, c.location.column, c.kind.value)
        if c.kind in (K.CALL_EXPR, K.UNARY_OPERATOR, K.UNION_DECL) + CASTS:
            if key in seen:
                return
            seen.add(key)
        if c.kind == K.CALL_EXPR:
            call(c)
        if c.kind == K.VAR_DECL and (c.storage_class == ci.StorageClass.STATIC or c.semantic_parent.kind in (K.TRANSLATION_UNIT, K.NAMESPACE)
                                     or (c.semantic_parent.kind in (K.CLASS_DECL, K.STRUCT_DECL, K.CLASS_TEMPLATE))):
            t = c.type.get_canonical()
            fixed = t.is_const_qualified()
            while t.kind in (TK.CONSTANTARRAY, TK.INCOMPLETEARRAY):
                t = t.get_array_element_type().get_canonical()
                fixed = fixed or t.is_const_qualified()
            own = c.tls_kind != ci.TLSKind.NONE or "atomic" in c.type.spelling or "atomic" in t.spelling
            if not fixed and t.kind != TK.LVALUEREFERENCE and not own and (c.get_usr(), "shared") not in seen:
                seen.add((c.get_usr(), "shared"))
                rel, line = at(c)
                text = "%s:%d: `%s` can be written and is one for every object and every thread:\n    %s" % (rel, line, c.spelling, line_at(path, line)[:150])
                (refused if path.startswith(STRONG_DIR) else shared).append(text)
        if os.path.basename(path) != "subarray.h":
            kept = None
            if c.kind == K.FIELD_DECL and window(c.type):
                kept = "a field"
            elif c.kind == K.VAR_DECL and window(c.type) and (c.storage_class == ci.StorageClass.STATIC
                                                              or c.semantic_parent.kind in (K.TRANSLATION_UNIT, K.NAMESPACE)):
                kept = "a global or a static"
            elif c.kind in (K.FUNCTION_DECL, K.CXX_METHOD) and window(c.result_type):
                kept = "what a function gives back"
            if c.kind == K.VAR_DECL and window(c.type) and not kept and c.type.get_canonical().kind == TK.RECORD \
                    and c.semantic_parent.kind not in (K.TRANSLATION_UNIT, K.NAMESPACE) and (path, c.location.line, c.location.column, "held") not in seen:
                seen.add((path, c.location.line, c.location.column, "held"))
                held(c)
            if c.kind == K.CXX_METHOD and c.is_definition() and (path, c.location.line, c.location.column, "leaves") not in seen:
                seen.add((path, c.location.line, c.location.column, "leaves"))
                leaving(c)
            if kept and (path, c.location.line, "kept") not in seen:
                seen.add((path, c.location.line, "kept"))
                rel, line = at(c)
                refused.append("%s:%d: a %s, a window on an array, is %s: it could outlive its array:\n    %s"
                               % (rel, line, window(c.type if kept != "what a function gives back" else c.result_type), kept, line_at(path, line)[:150]))
        if not path.startswith(STRONG_DIR):
            rel, line = at(c)
            what = None
            if c.kind == K.UNARY_OPERATOR:
                first = next(iter(c.get_tokens()), None)
                ch = list(c.get_children())
                if first is not None and first.spelling == "&" and len(ch) == 1:
                    r = proved_record(ch[0].type)
                    if r and ch[0].type.get_canonical().kind not in (TK.POINTER,):
                        what = "the address of a %s is taken" % r
            elif c.kind in (K.CXX_REINTERPRET_CAST_EXPR, K.CXX_CONST_CAST_EXPR, K.CSTYLE_CAST_EXPR, K.CXX_STATIC_CAST_EXPR):
                ch = [x for x in c.get_children() if x.kind not in (K.TYPE_REF, K.NAMESPACE_REF, K.TEMPLATE_REF)]
                if ch:                      # a pointer to one, or one itself (cast as a reference), made something else
                    r = proved_record(inner(ch[-1]).type) if inner(ch[-1]).type.get_canonical().kind in (TK.POINTER, TK.RECORD) else None
                    if r and proved_record(c.type) != r:
                        what = "a %s is cast to something else" % r
            elif c.kind == K.UNION_DECL:
                for m in c.get_children():
                    if m.kind == K.FIELD_DECL and proved_record(m.type):
                        what = "a %s is a member of a union" % proved_record(m.type)
            if what:
                refused.append("%s:%d: outside %s/, %s: its fields could be changed by other than its methods:\n    %s"
                               % (rel, line, STRONG.strip("/"), what, line_at(path, line)[:150]))
    for ch in c.get_children():
        visit(ch)


configure_libclang()
index = ci.Index.create()
builtin = probe([os.environ.get("CC", "cc"), "-print-resource-dir"], "-resource-dir") \
    or probe([os.environ.get("CC", "cc"), "-print-file-name=include"], "-isystem")
flags = ["-x", "c++", "-std=" + os.environ.get("STD", "gnu++20"), "-Wno-everything", "-I" + SUBJECT]
flags += ["-I" + d for d in os.environ.get("INCLUDE", "").split(":") if d] + builtin

files, texts = [], {}
for root, _, names in sorted(os.walk(SUBJECT)):
    for f in sorted(names):
        if f.endswith(SOURCES + HEADERS):
            path = os.path.realpath(os.path.join(root, f))
            files.append(path)
            texts[path] = plain(open(path, encoding="utf-8", errors="replace").read())

# one owner: threads and signal handlers by the words, in every file
handlers, threads = [], []
for path in files:
    rel = os.path.relpath(path, SUBJECT)
    for i, line in enumerate(texts[path].split("\n")):
        if re.search(THREADS, line):
            threads.append("%s:%d: %s" % (rel, i + 1, line_at(path, i + 1)[:150]))
        m = re.search(r"\bsignal\s*\(\s*[^,()]+,\s*([A-Za-z_]\w*)\s*\)", line)
        if (m and m.group(1) not in ("SIG_IGN", "SIG_DFL")) or re.search(r"\bsigaction\s*\(", line):
            handlers.append("%s:%d: %s" % (rel, i + 1, line_at(path, i + 1)[:150]))

# one name, own bytes: by Clang's reading. Each source, then each header no source brought in.
unread, reached = [], set()
for path in [p for p in files if p.endswith(SOURCES)] + [p for p in files if p.endswith(HEADERS)]:
    if path in reached:
        continue
    tu = index.parse(path, args=flags)
    errors = [d for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]
    if errors:
        unread.append("%s: %s" % (os.path.relpath(path, SUBJECT), errors[0].spelling))
    reached.add(path)
    for inc in tu.get_includes():
        reached.add(os.path.realpath(inc.include.name))
    visit(tu.cursor)

if threads and shared:
    for x in threads:
        refused.append("%s\n    a thread is started, and there is state that can be written and is one for every thread (%d: the first is %s)"
                       % (x, len(set(shared)), sorted(set(shared))[0].split(": ")[0]))
for r in unread:
    print("lint: could not be read whole (set INCLUDE to where its #includes are): %s" % r)
for r in sorted(set(refused)):
    print("lint: " + r)
if unread or refused:
    print("lint: REFUSED: %d. What is proved is proved alone; this is what lets it be." % (len(unread) + len(set(refused))))
    sys.exit(1)
print("lint: ok: %d files, %d calls, %d of them of what is under %s/: no two arguments of a call are one thing, "
      "no thread is started beside state all share, and nothing outside reaches a proved value's bytes" % (len(files), calls[0], calls[1], STRONG.strip("/")))
for title, lines in (("argument%s of what is proved not judged (not a name)", sorted(set(unjudged))),
                     ("window%s made by code that is not proved (that its elements are there, and stay, is that code's to keep)", sorted(set(made))),
                     ("method%s of a class that is not proved that give back what is of their own object", sorted(set(leaves))),
                     ("pair%s of arguments that are one thing, in calls of what is not this program's", sorted(set(said))),
                     ("thing%s that can be written and shared by every object and thread (so no thread may be started)", sorted(set(shared))),
                     ("thread%s started (that what each is handed is its alone is read by a person)", threads),
                     ("signal handler%s (each runs between any two steps: that it touches nothing proved is read by a person)", handlers)):
    if lines:
        print("lint: %d %s:" % (len(lines), title % ("" if len(lines) == 1 else "s")))
        for x in lines:
            print("    " + x.replace("\n    ", "  |  ")[:200])
