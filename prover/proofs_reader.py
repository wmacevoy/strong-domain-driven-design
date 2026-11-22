"""The reader of a proof file (model/forall.h; proofs.py's docstring says what is read): Clang's
cursors in, the tree of cxx.py's last section out. Every question asked of Clang about a proof, and
every refusal of one, is here; proofs.py writes what is owed from the tree and refuses nothing.

It reads in the order proofs.py did when it wrote as it read, so that of a file with several faults
the first refused is the one it always was. That order is not the text's in one place: at a loop
over an object already made, every statement of the body is first asked what it is, and then what
a round hands to the next is read, before the body is.

Its own helpers, not reader.py's, where the two do not behave the same: `strip` sees through casts
and `width` takes no bool and no int; a refusal says the file and line, not the column.
"""

import os
import re

from clang.cindex import CursorKind as K, TypeKind as TK

from clang_edge import operator_of
from cxx import (Cmp, Lit, LNot, Logic, Name,
                 AllBytes, AllValues, Ask, AskInv, CallFn, Choose, Do, Make, Proof, Prove, SeqSize, Window)

UNSIGNED = (TK.UCHAR, TK.USHORT, TK.UINT, TK.ULONG, TK.ULONGLONG)


class Refused(Exception):
    pass


def refuse(c, why):
    f = c.location.file
    raise Refused("%s:%d: %s" % (os.path.basename(f.name) if f else "?", c.location.line, why))


def strip(e):
    while e.kind in (K.UNEXPOSED_EXPR, K.PAREN_EXPR, K.CXX_FUNCTIONAL_CAST_EXPR, K.CXX_STATIC_CAST_EXPR):
        ch = [c for c in e.get_children() if c.kind not in (K.TYPE_REF, K.NAMESPACE_REF, K.TEMPLATE_REF)]
        if len(ch) != 1:
            return e
        e = ch[0]
    return e


def width(t, c):
    t = t.get_canonical()
    if t.kind not in UNSIGNED:
        refuse(c, "a number that is not an unsigned integer (`%s`)" % t.spelling)
    return t.get_size() * 8


def read(tu, source, klass, classes=None, functions=None):
    """Each PROOF( name ) of the file `source` (not of what it includes), read: a list of Proof.
    `klass` is the class (as the C++ names it) whose file this is. The proof is of a set of
    domains: that class, and `classes` and `functions` beside it, each {name in the C++: name it is
    proved under}, the domains proved before it. It may make objects of any of those classes and
    call any of those functions."""
    here = os.path.realpath(source)
    classes = dict(classes or {})
    classes.setdefault(klass[1] if isinstance(klass, tuple) else klass, klass[0] if isinstance(klass, tuple) else klass)
    out = []
    for c in tu.cursor.get_children():
        if (c.kind == K.FUNCTION_DECL and c.is_definition() and c.spelling.startswith("proof_")
                and c.location.file and os.path.realpath(c.location.file.name) == here):
            out.append(ProofReader(c, klass[1] if isinstance(klass, tuple) else klass, classes, functions or {}).read())
    return out


class ProofReader:
    """One PROOF, read. `made`, handed down, is the set of the objects made where a thing is read
    (their declarations' USRs); one made in a loop is not, after it, as no round of that loop is
    known to have run."""

    def __init__(self, fn, klass, classes, functions):
        self.fn, self.C = fn, klass
        self.classes = classes          # {a class's name in the C++: the name it is proved under}
        self.functions = functions      # the same, of functions
        self.bytes = set()              # the loop variables that are sequences of bytes
        self.length = {}                # of those, each that has a length, every_bytes( n ): n
        self.objs = {}                  # each object's declaration's USR: (its name, its class, proved under)
        self.obj = None                 # (kept for what reads one object: the first made)

    def set_names(self):
        return ", ".join(sorted(set(self.classes.values()) | set(self.functions.values())))

    # numbers ------------------------------------------------------------------------------------
    def wide(self, e):
        """The width a literal beside `e` is read at: `e`'s, if it says one."""
        e = strip(e)
        if e.kind == K.DECL_REF_EXPR:
            return width(e.type, e)
        if e.kind == K.CALL_EXPR:
            return width(e.type, e)
        if e.kind == K.CONDITIONAL_OPERATOR:
            _, a, b = list(e.get_children())
            return self.wide(a) or self.wide(b)
        return None

    def number(self, e, w, made):
        e = strip(e)
        if e.kind == K.INTEGER_LITERAL:
            if w is None:
                refuse(e, "a literal whose width nothing beside it says")
            text = "".join(t.spelling for t in e.get_tokens()).lower().rstrip("ul")
            return Lit(int(text, 0), w)
        if e.kind == K.DECL_REF_EXPR and e.referenced.kind == K.VAR_DECL and e.referenced.get_usr() not in self.objs:
            return Name(e.spelling, "var")
        if e.kind == K.CALL_EXPR and e.referenced is not None and e.referenced.spelling == "size":
            ch = list(e.get_children())
            on = strip(list(ch[0].get_children())[0]) if ch and ch[0].kind == K.MEMBER_REF_EXPR and list(ch[0].get_children()) else None
            if on is not None and on.kind == K.DECL_REF_EXPR and on.referenced.get_usr() in self.bytes:
                return SeqSize(on.spelling)
        if e.kind == K.CALL_EXPR and e.referenced is not None and e.referenced.kind == K.FUNCTION_DECL:
            f = e.referenced.spelling
            if f not in self.functions:
                refuse(e, "a call of `%s`, which is not a function of the set proved before this file (%s)" % (f, self.set_names()))
            params = list(e.referenced.get_arguments())
            return CallFn(self.functions[f], [self.number(a, width(p.type, a), made) for a, p in zip(e.get_arguments(), params)])
        if e.kind == K.CALL_EXPR:
            m, obj = self.method(e)
            if not m.is_const_method() or list(e.get_arguments()):
                refuse(e, "in a condition, a method that is not const, or takes something")
            if obj not in made:
                refuse(e, "the object is asked something before it is made")
            return Ask(m.spelling, *self.objs[obj][:1], self.objs[obj][1])
        if e.kind == K.CONDITIONAL_OPERATOR:
            c, a, b = list(e.get_children())
            return Choose(self.cond(c, made), self.number(a, w, made), self.number(b, w, made))
        refuse(e, "a number this does not read (a loop's variable, a literal, a const method of an object, a function of the set, `?:`)")

    def method(self, e):
        """A call of a method of an object made here: (the method, the object's USR)."""
        m = e.referenced
        ch = list(e.get_children())
        on = strip(list(ch[0].get_children())[0]) if ch and ch[0].kind == K.MEMBER_REF_EXPR and list(ch[0].get_children()) else None
        if m is None or m.kind != K.CXX_METHOD or on is None or on.kind != K.DECL_REF_EXPR or on.referenced.get_usr() not in self.objs:
            refuse(e, "a call that is not of a method of an object of the set (%s)" % self.set_names())
        return m, on.referenced.get_usr()

    def argument(self, a, p, made):
        """What a method is handed: a number; or, for a parameter that is a window on bytes, a Window."""
        t = p.type.get_canonical().spelling
        fixed = re.match(r"Strong::fixed<(\d+)[UL]*[,>]", t)
        if not (t.startswith("Strong::subarray<") or fixed or t in ("Bytes", "const Bytes")):
            return self.number(a, width(p.type, a), made)
        found = []
        def walk(c):
            if c.kind == K.DECL_REF_EXPR and c.referenced.kind == K.VAR_DECL:
                found.append(c)
            if c.kind == K.CALL_EXPR and c.referenced is not None and c.referenced.kind == K.CXX_METHOD and c.referenced.spelling not in ("data", "size"):
                refuse(c, "a window made of something other than `b.data(), b.size()`")
            for ch in c.get_children():
                walk(ch)
        walk(a)
        made_of = "".join(t.spelling for t in a.get_tokens())
        if fixed:       # N bytes by its type: made of where a sequence of N begins
            n = int(fixed.group(1))
            if len(found) != 1 or self.length.get(found[0].referenced.get_usr()) != n \
                    or not made_of.endswith("(%s.data())" % found[0].spelling):
                refuse(a, "a fixed window of %d bytes that is not `W( b.data() )` of one loop's sequence of every_bytes( %d )" % (n, n))
            return Window(found[0].spelling)
        if len(found) != 2 or found[0].referenced != found[1].referenced or found[0].referenced.get_usr() not in self.bytes \
                or not made_of.endswith("(%s.data(),%s.size())" % (found[0].spelling, found[0].spelling)):
            refuse(a, "a window that is not `W( b.data(), b.size() )` of one loop's sequence of bytes")
        return Window(found[0].spelling)

    # conditions ---------------------------------------------------------------------------------
    def cond(self, e, made):
        e = strip(e)
        if e.kind == K.BINARY_OPERATOR:
            a, b = list(e.get_children())
            op = operator_of(e)
            if op in ("&&", "||"):
                return Logic(op, self.cond(a, made), self.cond(b, made))
            if op in ("<=", "<", ">=", ">", "==", "!="):
                w = self.wide(a) or self.wide(b)
                return Cmp(op, self.number(a, w, made), self.number(b, w, made), False)
            refuse(e, "the operator `%s` in a condition" % op)
        if e.kind == K.UNARY_OPERATOR and next(iter(e.get_tokens())).spelling == "!":
            return LNot(self.cond(list(e.get_children())[0], made))
        if e.kind == K.CALL_EXPR and e.referenced is not None and e.referenced.spelling == "invariant":
            _, obj = self.method(e)
            if obj not in made:
                refuse(e, "the object is asked something before it is made")
            return AskInv(*self.objs[obj][:1], self.objs[obj][1])
        refuse(e, "a condition this does not read (comparisons, `&&`, `||`, `!`, `invariant()`)")

    # statements ---------------------------------------------------------------------------------
    @staticmethod
    def conjuncts(e):
        e = strip(e)
        if e.kind == K.BINARY_OPERATOR and operator_of(e) == "&&":
            a, b = list(e.get_children())
            return ProofReader.conjuncts(a) + ProofReader.conjuncts(b)
        return [e]

    @staticmethod
    def names(e, var):
        if e.kind == K.DECL_REF_EXPR and e.referenced == var:
            return True
        return any(ProofReader.names(c, var) for c in e.get_children())

    def kind(self, s):
        s = strip(s)
        if s.kind == K.DECL_STMT:
            return "make", s
        if s.kind == K.CXX_FOR_RANGE_STMT:
            return "loop", s
        if s.kind == K.CALL_EXPR and s.referenced is not None and s.referenced.spelling == "PROVE":
            return "prove", s
        if s.kind == K.CALL_EXPR:
            return "call", s
        refuse(s, "a statement this does not read (an object made, a loop over all<T>, a call of an object's method, PROVE)")

    def carried(self, loop_body, var):
        """The conditions a round hands to the next: of the PROVEs that end the body, each conjunct that does not name the loop's variable."""
        last = []
        for s in loop_body:
            k, s = self.kind(s)
            if k == "prove":
                last.append(s)
            else:
                last = []
        out = []
        for p in last:
            for c in self.conjuncts(list(p.get_arguments())[0]):
                if not self.names(c, var):
                    out.append(c)
        return out

    def stmts(self, cursors, made):
        """The statements, read in order: (the nodes, whether the object is made after them)."""
        out = []
        for c in cursors:
            node, made = self.stmt(c, made)
            out.append(node)
        return out, made

    def stmt(self, c, made):
        k, s = self.kind(c)
        if k == "make":
            v = [c for c in s.get_children() if c.kind == K.VAR_DECL]
            named = v[0].type.get_canonical().get_declaration().spelling if len(v) == 1 else None
            if len(v) != 1 or named not in self.classes:
                refuse(s, "what is made here is not one object of a class of the set (%s)" % self.set_names())
            if v[0].get_usr() in made:
                refuse(s, "what is made here is made again: each object once")
            self.objs[v[0].get_usr()] = (v[0].spelling, self.classes[named])
            self.obj = self.obj or v[0]
            by = [c for c in v[0].get_children() if c.kind == K.CALL_EXPR]
            args = []
            if by and list(by[0].get_arguments()):
                params = list(by[0].referenced.get_arguments())
                args = [self.number(a, width(p.type, a), made) for a, p in zip(by[0].get_arguments(), params)]
            return Make(v[0].spelling, args, self.classes[named]), made | {v[0].get_usr()}
        if k == "prove":
            return Prove(self.cond(list(s.get_arguments())[0], made)), made
        if k == "call":
            if s.referenced is not None and s.referenced.kind == K.FUNCTION_DECL:
                refuse(s, "a function called as a statement: what it gives is kept nowhere (call it in a PROVE)")
            m, obj = self.method(s)
            if obj not in made:
                refuse(s, "the object is used before it is made")
            params = list(m.get_arguments())
            args = [self.argument(a, p, made) for a, p in zip(s.get_arguments(), params)]
            name, klass = self.objs[obj]
            return Do(m.spelling, m.result_type.get_canonical().kind == TK.VOID, args, name, klass), made
        # a loop
        parts = list(s.get_children())
        var = [c for c in parts if c.kind == K.VAR_DECL]
        body = [c for c in parts if c.kind == K.COMPOUND_STMT]
        if len(var) != 1 or len(body) != 1:
            refuse(s, "a loop that is not `for ( T x : all<T>() ) { ... }`")
        var, body = var[0], list(body[0].get_children())
        over = [c for c in parts if c.kind not in (K.VAR_DECL, K.COMPOUND_STMT)]
        seq = "vector<unsigned char" in var.type.get_canonical().spelling
        w = None if seq else width(var.type, var)
        ctor = None
        def find(c):
            nonlocal ctor
            if c.kind == K.CALL_EXPR and c.referenced is not None and c.referenced.kind == K.CONSTRUCTOR and ctor is None:
                ctor = c
            for ch in c.get_children():
                find(ch)
        for c in over:
            find(c)
        if seq:
            if ctor is None or ctor.type.get_canonical().spelling != "every_bytes":
                refuse(s, "a loop of sequences of bytes over something other than every_bytes() or every_bytes( n )")
            self.bytes.add(var.get_usr())
            given = list(ctor.get_arguments())
            if given:
                e = strip(given[0])
                if e.kind != K.INTEGER_LITERAL:
                    refuse(s, "every_bytes( n ) of an n that is not a number written out")
                self.length[var.get_usr()] = int("".join(t.spelling for t in e.get_tokens()).lower().rstrip("ul"), 0)
        elif ctor is None or not ctor.type.get_canonical().spelling.startswith("all<"):
            refuse(s, "a loop over something other than all<T>() or all<T>( a, b )")
        bounds = [] if seq else list(ctor.get_arguments())
        if bounds:
            bounds = [self.number(bounds[0], w, frozenset()), self.number(bounds[1], w, frozenset())]
        keep = [self.cond(c, made) for c in self.carried(body, var)] if made else []
        inside, _ = self.stmts(body, made)
        if seq:
            node = AllBytes(var.spelling, inside, keep, s.location.line, self.length.get(var.get_usr()))
        else:
            node = AllValues(var.spelling, w, bounds, inside, keep, s.location.line)
        return node, made

    def read(self):
        body = [c for c in self.fn.get_children() if c.kind == K.COMPOUND_STMT]
        if len(body) != 1:
            refuse(self.fn, "a PROOF with no body")
        stmts, _ = self.stmts(list(body[0].get_children()), frozenset())
        return Proof(self.fn.spelling[len("proof_"):], stmts)
