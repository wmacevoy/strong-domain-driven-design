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
             a pair is said, not refused: `execl( shell, shell, ... )` is how that is called.
  one thread Nothing starts a thread (std::thread, std::jthread, std::async, pthread_create): so
             for as long as a method runs, what it reads is changed by it or by nothing. Refused
             anywhere under SUBJECT. A signal handler that is a function is said, each one: it
             runs between any two steps, and that it touches nothing proved is read by a person.
  own bytes  Outside STRONG, a value of a class declared under STRONG is reached by its methods
             and by copying it whole, and no other way: its address is not taken, a pointer or
             reference to it is not cast, and it is not a member of a union. So its fields are
             changed by its own methods and by nothing else. Refused otherwise.

  a window   A window on an array (a class of STRONG's subarray.h, which keeps a pointer) does not
             outlive its array: it is a local or a parameter, never a field, never a global or a
             static, never what a function gives back. And outside STRONG only its `_checked`
             kind is made, and nothing of it is called: it is made and handed over. Refused
             otherwise. (That its array is as large as its type says is the compiler's.)

It reads what is written at the call (SE1/U4, chosen), by Clang's library. So it does not see
  - one thing reached by two names (two pointers that were made equal somewhere else);
  - an argument that is not a name (a sum, a call's pointer result): each is said, "not judged";
  - bytes written over a struct that has a proved value in it (memset of the struct whole);
  - a reference into a container that is then made to grow.
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
        if n in ("c_str", "data", "front", "back", "begin") and ch and ch[0].kind == K.MEMBER_REF_EXPR:
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
refused, said, unjudged = [], [], []
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
        name = f.semantic_parent.spelling if f.kind == K.CONSTRUCTOR else f.spelling
        if "_checked" not in name:
            refused.append("%s:%d: outside %s/, %s of a window on an array: there only its `_checked` kind is made, and handed over:\n    %s"
                           % (rel, line, STRONG.strip("/"), "a %s is made" % name if f.kind == K.CONSTRUCTOR else "%s is called" % name,
                              line_at(c.location.file.name, line)[:150]))
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
            (refused if ours else said).append(text)


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
        if os.path.basename(path) != "subarray.h":
            kept = None
            if c.kind == K.FIELD_DECL and window(c.type):
                kept = "a field"
            elif c.kind == K.VAR_DECL and window(c.type) and (c.storage_class == ci.StorageClass.STATIC
                                                              or c.semantic_parent.kind in (K.TRANSLATION_UNIT, K.NAMESPACE)):
                kept = "a global or a static"
            elif c.kind in (K.FUNCTION_DECL, K.CXX_METHOD) and window(c.result_type):
                kept = "what a function gives back"
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

# one thread: by the words, in every file
handlers = []
for path in files:
    rel = os.path.relpath(path, SUBJECT)
    for i, line in enumerate(texts[path].split("\n")):
        if re.search(THREADS, line):
            refused.append("%s:%d: a thread is started: what a method reads could be changed while it runs:\n    %s"
                           % (rel, i + 1, line_at(path, i + 1)[:150]))
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

for r in unread:
    print("lint: could not be read whole (set INCLUDE to where its #includes are): %s" % r)
for r in sorted(set(refused)):
    print("lint: " + r)
if unread or refused:
    print("lint: REFUSED: %d. What is proved is proved alone; this is what lets it be." % (len(unread) + len(set(refused))))
    sys.exit(1)
print("lint: ok: %d files, %d calls, %d of them of what is under %s/: no two arguments of a call are one thing, "
      "nothing starts a thread, and nothing outside reaches a proved value's bytes" % (len(files), calls[0], calls[1], STRONG.strip("/")))
for title, lines in (("argument%s of what is proved not judged (not a name)", sorted(set(unjudged))),
                     ("pair%s of arguments that are one thing, in calls of what is not this program's", sorted(set(said))),
                     ("signal handler%s (each runs between any two steps: that it touches nothing proved is read by a person)", handlers)):
    if lines:
        print("lint: %d %s:" % (len(lines), title % ("" if len(lines) == 1 else "s")))
        for x in lines:
            print("    " + x.replace("\n    ", "  |  ")[:200])
