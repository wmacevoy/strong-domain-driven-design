"""
The questions of a cursor or a type that more than one rule asks, and Program: where the program is.

Nothing here keeps what a rule found. What is stateless is a function; what needs SUBJECT or STRONG
is a method of Program, which is made once, by lint.py, and handed to each rule.
"""
import os
import re

from clang.cindex import CursorKind as K, TypeKind as TK

SKIP = (K.UNEXPOSED_EXPR, K.PAREN_EXPR, K.CXX_STATIC_CAST_EXPR, K.CXX_REINTERPRET_CAST_EXPR,
        K.CXX_CONST_CAST_EXPR, K.CSTYLE_CAST_EXPR, K.CXX_FUNCTIONAL_CAST_EXPR)
CASTS = (K.CXX_REINTERPRET_CAST_EXPR, K.CXX_CONST_CAST_EXPR, K.CSTYLE_CAST_EXPR, K.CXX_STATIC_CAST_EXPR)
FUNCTIONS = (K.FUNCTION_DECL, K.CXX_METHOD, K.CONSTRUCTOR, K.DESTRUCTOR, K.FUNCTION_TEMPLATE)
CALLABLE = (K.FUNCTION_DECL, K.CXX_METHOD, K.CONSTRUCTOR, K.FUNCTION_TEMPLATE)
NOT_EXPRESSION = (K.TYPE_REF, K.NAMESPACE_REF, K.TEMPLATE_REF)


def plain(text):
    """The text with comments and what is in quotes made blank, no line moved."""
    def blank(m):
        return re.sub(r"[^\n]", " ", m.group(0))
    return re.sub(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\\n])*"|\'(?:\\.|[^\'\\\n])*\'', blank, text, flags=re.S)


def inner(e):
    """The expression inside brackets, casts and what the compiler wrote around it."""
    while e.kind in SKIP:
        ch = [c for c in e.get_children() if c.kind not in NOT_EXPRESSION]
        if len(ch) != 1:
            return e
        e = ch[0]
    return e


def words(e):
    return " ".join(t.spelling for t in e.get_tokens())


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


def line_at(path, n):
    try:
        return open(path, encoding="utf-8", errors="replace").read().split("\n")[n - 1].strip()
    except OSError:
        return ""


def function_of(c):
    p = c.semantic_parent
    while p is not None and p.kind not in (K.FUNCTION_DECL, K.CXX_METHOD, K.CONSTRUCTOR, K.DESTRUCTOR, K.FUNCTION_TEMPLATE, K.TRANSLATION_UNIT):
        p = p.semantic_parent
    return p if p is not None and p.kind != K.TRANSLATION_UNIT else None


def callee(c):
    """What a call expression calls, if it is a function, a method, a constructor or a template of one; else None."""
    f = c.referenced
    if f is None or f.kind not in CALLABLE:
        return None
    return f


class Program:
    """Where the program is: SUBJECT (its directory), and STRONG (the directory under it where what is proved stands)."""

    def __init__(self, subject, strong):
        self.subject = os.path.realpath(subject)
        self.subject_dir = self.subject + os.sep
        self.strong_name = strong.strip("/")            # as it is written in a message
        self.strong_dir = os.path.join(self.subject, self.strong_name) + os.sep

    def under_strong(self, cursor):
        f = cursor.location.file
        return f is not None and os.path.realpath(f.name).startswith(self.strong_dir)

    def at(self, c):
        return os.path.relpath(os.path.realpath(c.location.file.name), self.subject), c.location.line

    def proved_record(self, t):
        """The class declared under STRONG that this type is, or points or refers to; or None."""
        t = t.get_canonical()
        while t.kind in (TK.POINTER, TK.LVALUEREFERENCE, TK.RVALUEREFERENCE, TK.CONSTANTARRAY, TK.INCOMPLETEARRAY):
            t = t.get_pointee() if t.kind in (TK.POINTER, TK.LVALUEREFERENCE, TK.RVALUEREFERENCE) else t.element_type
            t = t.get_canonical()
        d = t.get_declaration()
        if d is None or d.kind not in (K.CLASS_DECL, K.STRUCT_DECL, K.CLASS_TEMPLATE) or not self.under_strong(d):
            return None
        if os.path.basename(d.location.file.name) == "caller.h":      # who called: not proved, and nothing kept
            return None
        return d.spelling

    def window(self, t):
        """The class of STRONG's subarray.h that this type is, or points or refers to, or is an array of; or None."""
        t = t.get_canonical()
        while t.kind in (TK.POINTER, TK.LVALUEREFERENCE, TK.RVALUEREFERENCE, TK.CONSTANTARRAY, TK.INCOMPLETEARRAY):
            t = t.get_pointee() if t.kind in (TK.POINTER, TK.LVALUEREFERENCE, TK.RVALUEREFERENCE) else t.element_type
            t = t.get_canonical()
        d = t.get_declaration()
        if d is None or d.location.file is None or not self.under_strong(d) or os.path.basename(d.location.file.name) != "subarray.h":
            return None
        return d.spelling

    def name_of(self, e):
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
            base = self.name_of(ch[0]) if ch else ("this", [])
            return None if base is None else (base[0], base[1] + [d.spelling])
        if e.kind == K.UNARY_OPERATOR:
            ch = list(e.get_children())
            first = next(iter(e.get_tokens()), None)
            if first is not None and first.spelling in ("&", "*") and len(ch) == 1:
                return self.name_of(ch[0])
            return None
        if e.kind == K.BINARY_OPERATOR:            # a pointer and a number: still in what the pointer is in
            ch = list(e.get_children())
            if len(ch) == 2 and e.type.get_canonical().kind == TK.POINTER:
                return self.name_of(ch[0]) or self.name_of(ch[1])
            return None
        if e.kind == K.ARRAY_SUBSCRIPT_EXPR:
            ch = list(e.get_children())
            base = self.name_of(ch[0])
            return None if base is None else (base[0], base[1] + ["[" + words(ch[1]) + "]"])
        if e.kind == K.CALL_EXPR and e.referenced is not None:
            n = e.referenced.spelling
            given, ch = list(e.get_arguments()), list(e.get_children())
            if n == "operator[]" and len(given) == 2:
                base = self.name_of(given[0])
                return None if base is None else (base[0], base[1] + ["[" + words(given[1]) + "]"])
            if n in ("operator->", "operator*") and len(given) == 1:
                return self.name_of(given[0])
            if n in ("c_str", "data", "front", "back", "begin", "end", "find", "at", "rbegin", "lower_bound", "upper_bound") and ch and ch[0].kind == K.MEMBER_REF_EXPR \
                    and not (e.referenced.location.file and os.path.realpath(e.referenced.location.file.name).startswith(self.subject_dir)):
                sub = list(ch[0].get_children())       # the bytes a string or a vector keeps: some part of it
                base = self.name_of(sub[0]) if sub else ("this", [])
                return None if base is None else (base[0], base[1] + ["*"])
        return None
