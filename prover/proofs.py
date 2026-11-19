#!/usr/bin/env python3
"""
proofs -- what is claimed of a class, written as a test that cannot be run, made what is owed.

    python3 proofs.py proofs/C.proof.cpp --class C -o gen [-I dir]...      writes gen/CProofOwed.lean

The file is C++ (model/forall.h makes it compile): each `PROOF( name ) { ... }` is a test of the
class C that steps through every value of its loops' types, so nobody can run it. This reads it
as it would run, and writes in Lean what must be proved for every PROVE in it to hold in every
round: `C Proof.Owed`, over the model prooc.py made of the class (gen/CModel.lean). A claims
file proves that, and is audited as any other (prove.sh).

What a loop is made into. A loop over every x cannot be followed round by round, so it is proved
by what holds from one round to the next:
  - at the loop: the class's invariant holds, and so does each "carried" condition: a conjunct of
    the PROVEs that end the loop's body which does not name the loop's own variable;
  - one statement per loop: from ANY state of which those hold, for every x, the body's PROVEs
    hold, and at its end those hold again;
  - after the loop: the state is any of which those hold, and no more is known.
So each PROVE holds in every round, by induction on the rounds. An object made inside a loop is
new in each round, and nothing is carried.

It reads a subset, and refuses the rest, saying where: one object of the class, made by
`C name;` or `C name( ... );`; `for ( T x : all<T>() )` and `all<T>( a, b )` with T an unsigned
integer and a, b literals; `for ( const std::vector<unsigned char>& b : every_bytes() )`, every
sequence of bytes of every length; calls of the object's methods with arguments that are loop
variables or literals, or a window on such bytes (`W( b.data(), b.size() )`, for a parameter that
is a Strong::subarray or a Bytes). A call says that the method ends and commits no memory error:
where its model takes `fuel`, that some number of rounds is enough; `PROVE( condition )`, a condition of comparisons, `&&`, `||`, `!`, `?:`, the
object's const methods that take nothing, and `invariant()`.
"""
import argparse
import ctypes
import os
import re
import sys

import clang.cindex as ci
from clang.cindex import CursorKind as K, TypeKind as TK

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oopcc import configure_libclang, probe   # noqa: E402

UNSIGNED = (TK.UCHAR, TK.USHORT, TK.UINT, TK.ULONG, TK.ULONGLONG)
WORDS = set("at end from to in do then else if fun let have show match with where by def theorem open".split())


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


def operator(c):
    lib = ci.conf.lib
    lib.clang_getCursorBinaryOperatorKind.argtypes = [ci.Cursor]
    lib.clang_getCursorBinaryOperatorKind.restype = ctypes.c_int
    lib.clang_getBinaryOperatorKindSpelling.argtypes = [ctypes.c_int]
    lib.clang_getBinaryOperatorKindSpelling.restype = ci._CXString
    text = lib.clang_getCString(lib.clang_getBinaryOperatorKindSpelling(lib.clang_getCursorBinaryOperatorKind(c)))
    return text.decode("utf-8") if isinstance(text, bytes) else text


def width(t, c):
    t = t.get_canonical()
    if t.kind not in UNSIGNED:
        refuse(c, "a number that is not an unsigned integer (`%s`)" % t.spelling)
    return t.get_size() * 8


def lean(name):
    return name + "'" if name in WORDS else name


class Proof:
    def __init__(self, fn, klass, fuelled=()):
        self.fn, self.C, self.fuelled = fn, klass, set(fuelled)
        self.bytes = set()              # the loop variables that are sequences of bytes
        self.name = fn.spelling[len("proof_"):]
        self.owed = []                  # (name, what it says, the statement)
        self.n = 0
        self.loops = 0
        self.obj = None                 # the object's declaration

    def fresh(self, stem):
        self.n += 1
        return "%s%d" % (stem, self.n)

    # numbers ------------------------------------------------------------------------------------
    def wide(self, e):
        e = strip(e)
        if e.kind == K.DECL_REF_EXPR:
            return width(e.type, e)
        if e.kind == K.CALL_EXPR:
            return width(e.type, e)
        if e.kind == K.CONDITIONAL_OPERATOR:
            _, a, b = list(e.get_children())
            return self.wide(a) or self.wide(b)
        return None

    def number(self, e, w, state, gets):
        e = strip(e)
        if e.kind == K.INTEGER_LITERAL:
            if w is None:
                refuse(e, "a literal whose width nothing beside it says")
            text = "".join(t.spelling for t in e.get_tokens()).lower().rstrip("ul")
            return "%d#%d" % (int(text, 0), w)
        if e.kind == K.DECL_REF_EXPR and e.referenced.kind == K.VAR_DECL and e.referenced != self.obj:
            return lean(e.spelling)
        if e.kind == K.CALL_EXPR and e.referenced is not None and e.referenced.spelling == "size":
            ch = list(e.get_children())
            on = strip(list(ch[0].get_children())[0]) if ch and ch[0].kind == K.MEMBER_REF_EXPR and list(ch[0].get_children()) else None
            if on is not None and on.kind == K.DECL_REF_EXPR and on.referenced.get_usr() in self.bytes:
                return "(Prooc.Bytes.size %s)" % lean(on.spelling)     # how many bytes a loop's sequence has
        if e.kind == K.CALL_EXPR:
            m = self.method(e)
            if not m.is_const_method() or list(e.get_arguments()):
                refuse(e, "in a condition, a method that is not const, or takes something")
            if state is None:
                refuse(e, "the object is asked something before it is made")
            r = self.fresh("r")
            gets.append("%s.%s %s = some (%s, %s)" % (self.C, m.spelling, state, state, r))
            return r
        if e.kind == K.CONDITIONAL_OPERATOR:
            c, a, b = list(e.get_children())
            return "(if %s then %s else %s)" % (self.cond(c, state, gets), self.number(a, w, state, gets), self.number(b, w, state, gets))
        refuse(e, "a number this does not read (a loop's variable, a literal, a const method of the object, `?:`)")

    def method(self, e):
        m = e.referenced
        ch = list(e.get_children())
        on = strip(list(ch[0].get_children())[0]) if ch and ch[0].kind == K.MEMBER_REF_EXPR and list(ch[0].get_children()) else None
        if m is None or m.kind != K.CXX_METHOD or on is None or on.kind != K.DECL_REF_EXPR or on.referenced != self.obj:
            refuse(e, "a call that is not of a method of the one object of %s" % self.C)
        return m

    def argument(self, a, p, state):
        """What a method is handed: a number; or, for a parameter that is a window on bytes, the bytes it is a window on."""
        t = p.type.get_canonical().spelling
        if not (t.startswith("Strong::subarray<") or t in ("Bytes", "const Bytes")):
            return self.number(a, width(p.type, a), state, [])
        found = []
        def walk(c):
            if c.kind == K.DECL_REF_EXPR and c.referenced.kind == K.VAR_DECL:
                found.append(c)
            if c.kind == K.CALL_EXPR and c.referenced is not None and c.referenced.kind == K.CXX_METHOD and c.referenced.spelling not in ("data", "size"):
                refuse(c, "a window made of something other than `b.data(), b.size()`")
            for ch in c.get_children():
                walk(ch)
        walk(a)
        made = "".join(t.spelling for t in a.get_tokens())
        if len(found) != 2 or found[0].referenced != found[1].referenced or found[0].referenced.get_usr() not in self.bytes \
                or not made.endswith("(%s.data(),%s.size())" % (found[0].spelling, found[0].spelling)):
            refuse(a, "a window that is not `W( b.data(), b.size() )` of one loop's sequence of bytes")
        return lean(found[0].spelling)

    # conditions ---------------------------------------------------------------------------------
    def cond(self, e, state, gets):
        e = strip(e)
        if e.kind == K.BINARY_OPERATOR:
            a, b = list(e.get_children())
            op = operator(e)
            if op in ("&&", "||"):
                return "(%s %s %s)" % (self.cond(a, state, gets), "∧" if op == "&&" else "∨", self.cond(b, state, gets))
            if op in ("<=", "<", ">=", ">", "==", "!="):
                w = self.wide(a) or self.wide(b)
                sign = {"<=": "≤", ">=": "≥", "==": "=", "!=": "≠"}.get(op, op)
                return "(%s %s %s)" % (self.number(a, w, state, gets), sign, self.number(b, w, state, gets))
            refuse(e, "the operator `%s` in a condition" % op)
        if e.kind == K.UNARY_OPERATOR and next(iter(e.get_tokens())).spelling == "!":
            return "(¬ %s)" % self.cond(list(e.get_children())[0], state, gets)
        if e.kind == K.CALL_EXPR and e.referenced is not None and e.referenced.spelling == "invariant":
            self.method(e)
            if state is None:
                refuse(e, "the object is asked something before it is made")
            return "%s.Inv %s" % (self.C, state)
        refuse(e, "a condition this does not read (comparisons, `&&`, `||`, `!`, `invariant()`)")

    def holds(self, e, state):
        """A condition, with what its const methods give named: they run, leave the object, and give these."""
        gets = []
        text = self.cond(e, state, gets)
        if not gets:
            return text
        names = " ".join(g.rsplit(", ", 1)[1].rstrip(")") for g in gets)
        return "(∃ %s, %s ∧ %s)" % (names, " ∧ ".join(gets), text)

    # statements ---------------------------------------------------------------------------------
    @staticmethod
    def conjuncts(e):
        e = strip(e)
        if e.kind == K.BINARY_OPERATOR and operator(e) == "&&":
            a, b = list(e.get_children())
            return Proof.conjuncts(a) + Proof.conjuncts(b)
        return [e]

    @staticmethod
    def names(e, var):
        if e.kind == K.DECL_REF_EXPR and e.referenced == var:
            return True
        return any(Proof.names(c, var) for c in e.get_children())

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
        refuse(s, "a statement this does not read (an object made, a loop over all<T>, a call of the object's method, PROVE)")

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

    def chain(self, stmts, state, binders, end):
        if not stmts:
            return end(state)
        k, s = self.kind(stmts[0])
        rest = stmts[1:]
        if k == "make":
            v = [c for c in s.get_children() if c.kind == K.VAR_DECL]
            if len(v) != 1 or v[0].type.get_canonical().get_declaration().spelling != self.C or state is not None:
                refuse(s, "what is made here is one object of %s, once" % self.C)
            self.obj = v[0]
            made = [c for c in v[0].get_children() if c.kind == K.CALL_EXPR]
            args = ""
            if made and list(made[0].get_arguments()):
                params = list(made[0].referenced.get_arguments())
                args = "".join(" (%s)" % self.number(a, width(p.type, a), None, []) for a, p in zip(made[0].get_arguments(), params))
            g = self.fresh(lean(v[0].spelling))
            return "(∃ %s, %s.new%s = some %s ∧ %s)" % (g, self.C, args, g, self.chain(rest, g, binders, end))
        if k == "prove":
            return "(%s ∧ %s)" % (self.holds(list(s.get_arguments())[0], state), self.chain(rest, state, binders, end))
        if k == "call":
            m = self.method(s)
            if state is None:
                refuse(s, "the object is used before it is made")
            params = list(m.get_arguments())
            args = "".join(" (%s)" % self.argument(a, p, state) for a, p in zip(s.get_arguments(), params))
            g = self.fresh(lean(self.obj.spelling))
            fuel, some = ("fuel ", "fuel ") if m.spelling in self.fuelled else ("", "")
            if m.result_type.get_canonical().kind == TK.VOID:
                return "(∃ %s%s, %s.%s %s%s%s = some (%s, ()) ∧ %s)" % (fuel, g, self.C, m.spelling, some, state, args, g, self.chain(rest, g, binders, end))
            r = self.fresh("r")
            return "(∃ %s%s %s, %s.%s %s%s%s = some (%s, %s) ∧ %s)" % (fuel, g, r, self.C, m.spelling, some, state, args, g, r, self.chain(rest, g, binders, end))
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
        made = None
        def find(c):
            nonlocal made
            if c.kind == K.CALL_EXPR and c.referenced is not None and c.referenced.kind == K.CONSTRUCTOR and made is None:
                made = c
            for ch in c.get_children():
                find(ch)
        for c in over:
            find(c)
        if seq:
            if made is None or made.type.get_canonical().spelling != "every_bytes":
                refuse(s, "a loop of sequences of bytes over something other than every_bytes()")
            self.bytes.add(var.get_usr())
        elif made is None or not made.type.get_canonical().spelling.startswith("all<"):
            refuse(s, "a loop over something other than all<T>() or all<T>( a, b )")
        bounds = list(made.get_arguments())
        x = lean(var.spelling)
        within = []
        if bounds:
            within = ["%s ≤ %s" % (self.number(bounds[0], w, None, []), x), "%s ≤ %s" % (x, self.number(bounds[1], w, None, []))]
        self.loops += 1
        name = "%s_loop%d" % (self.name, self.loops)
        inner = binders + [(x, "Prooc.Bytes" if seq else "BitVec %d" % w)]
        keep = self.carried(body, var) if state is not None else []
        if state is None:
            said = self.chain(body, None, inner, lambda st: "True")
            self.owed.append((name, "the loop over `%s` at line %d: in every round" % (var.spelling, s.location.line),
                              "∀ %s, %s%s" % (" ".join("(%s : %s)" % b for b in inner), "".join(h + " → " for h in within), said)))
            return self.chain(rest, None, binders, end)
        g = self.fresh(lean(self.obj.spelling))
        def again(st):
            return "(%s)" % " ∧ ".join(["%s.Inv %s" % (self.C, st)] + [self.holds(c, st) for c in keep])
        given = ["%s.Inv %s" % (self.C, g)] + [self.holds(c, g) for c in keep] + within
        said = self.chain(body, g, inner, again)
        self.owed.append((name, "the loop over `%s` at line %d: from any state the rounds before could leave, in every round, and it leaves such a state"
                          % (var.spelling, s.location.line),
                          "∀ %s (%s : %s), %s%s" % (" ".join("(%s : %s)" % b for b in inner), g, self.C, "".join(h + " → " for h in given), said)))
        after = self.fresh(lean(self.obj.spelling))
        return "(%s ∧ (∀ %s : %s, %s%s))" % (again(state), after, self.C,
                                                "".join(h + " → " for h in ["%s.Inv %s" % (self.C, after)] + [self.holds(c, after) for c in keep]),
                                                self.chain(rest, after, binders, end))

    def read(self):
        body = [c for c in self.fn.get_children() if c.kind == K.COMPOUND_STMT]
        if len(body) != 1:
            refuse(self.fn, "a PROOF with no body")
        whole = self.chain(list(body[0].get_children()), None, [], lambda st: "True")
        return [(self.name, "PROOF( %s ), up to and between its loops" % self.name, whole)] + self.owed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("source")
    ap.add_argument("--class", dest="klass", required=True)
    ap.add_argument("-o", "--out", default="gen")
    ap.add_argument("-I", dest="include", action="append", default=[])
    ap.add_argument("--std", default="c++17")
    ap.add_argument("--model", help="the class's model, to know which methods take fuel (default: OUT/CModel.lean)")
    args = ap.parse_args()
    configure_libclang()
    builtin = probe([os.environ.get("CC", "cc"), "-print-resource-dir"], "-resource-dir") \
        or probe([os.environ.get("CC", "cc"), "-print-file-name=include"], "-isystem")
    tu = ci.Index.create().parse(args.source, args=["-x", "c++", "-std=" + args.std] + ["-I" + d for d in args.include] + builtin)
    errors = [d for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]
    if errors:
        sys.exit("proofs: %s does not compile: %s" % (args.source, errors[0].spelling))
    here = os.path.realpath(args.source)
    model = args.model or os.path.join(args.out, "%sModel.lean" % args.klass)
    fuelled = re.findall(r"^def (\w+) \(fuel : Nat\)", open(model).read(), flags=re.M) if os.path.exists(model) else []
    owed, proofs = [], 0
    try:
        for c in tu.cursor.get_children():
            if (c.kind == K.FUNCTION_DECL and c.is_definition() and c.spelling.startswith("proof_")
                    and c.location.file and os.path.realpath(c.location.file.name) == here):
                owed += Proof(c, args.klass, fuelled).read()
                proofs += 1
    except Refused as e:
        sys.exit("proofs: REFUSED: %s" % e)
    if not owed:
        sys.exit("proofs: %s has no PROOF( name ) { ... }" % args.source)
    C = args.klass
    L = ["import %sModel" % C, "",
         "/-! GENERATED by prover/proofs.py from %s. Do not edit." % os.path.basename(args.source),
         "WHAT MUST BE PROVEN for every PROVE of that file to hold in every round of its loops, were it",
         "run: this file imports the model of %s, and nothing written by hand. A loop is one statement:" % C,
         "from any state the rounds before could leave (the class's invariant, and what the loop's last",
         "PROVEs say without naming its variable), every round's PROVEs hold, and it leaves such a state. -/", "",
         "structure %sProof.Owed : Prop where" % C]
    owed = [o for o in owed if o[2].split(", ")[-1] != "True" or "∃" in o[2]]      # (a loop that only holds other loops says nothing of its own)
    for name, what, text in owed:
        L += ["  /-- %s. -/" % what, "  %s : %s" % (name, text)]
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "%sProofOwed.lean" % C), "w").write("\n".join(L) + "\n")
    print("%sProofOwed.lean: %d statements from %d PROOFs" % (C, len(owed), proofs))


if __name__ == "__main__":
    main()
