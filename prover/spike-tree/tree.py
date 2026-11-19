#!/usr/bin/env python3
"""
tree -- a SPIKE (2026-11-18): copy a class's methods out of the compiler's reading as trees, for
Cxx.lean, and ask the kernel two things of each.

    python3 spike-tree/tree.py model/Gauge.hpp -o gen        writes gen/GaugeTree.lean

For each method (and the constructor, and the invariant) it writes:
  C.tree_M     the method's body as a Cxx.Stmt: its words, in the shape the compiler read them in
  C.M_text     that the tree, written back as words, is the method's body word for word: so this
               program copied rightly. The words on the right are the compiler's own tokens of the
               source; nothing here chose them
  C.M_agrees   that what Cxx.lean says the tree means is the model prooc.py wrote: so the model,
               and every proof about it, is about the meaning said there, once

This program says nothing of what C++ means. It gives no meaning to an operator, and resolves no
name: `level` is the word "level", and Cxx.lean says what a word stands for. The one thing it adds
that has no word in the source is a conversion C++ makes unasked (`level = 0`: an int to a
uint32_t), which it takes from the compiler's tree.
"""
import argparse
import ctypes
import os
import sys

import clang.cindex as ci
from clang.cindex import CursorKind as CK, TypeKind as TK, TokenKind

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from clang_edge import configure_libclang, probe   # noqa: E402

TY = {TK.UCHAR: "u8", TK.USHORT: "u16", TK.UINT: "u32", TK.ULONG: "u64", TK.ULONGLONG: "u64", TK.INT: "int"}
WIDTH = {"u8": 8, "u16": 16, "u32": 32, "u64": 64}
BIN = {"+": "add", "-": "sub", "*": "mul", "&": "and", "|": "or", "^": "xor"}
CMP = {"<": "lt", "<=": "le", ">": "gt", ">=": "ge", "==": "eq", "!=": "ne"}


class No(Exception):
    pass


def no(c, why):
    raise No("%s:%d: %s" % (c.location.file.name if c.location.file else "?", c.location.line, why))


def ty(t, c):
    k = t.get_canonical().kind
    if k not in TY:
        no(c, "a type the spike does not copy: %s" % t.spelling)
    return TY[k]


def operator(c):
    lib = ci.conf.lib
    lib.clang_getCursorBinaryOperatorKind.argtypes = [ci.Cursor]
    lib.clang_getCursorBinaryOperatorKind.restype = ctypes.c_int
    lib.clang_getBinaryOperatorKindSpelling.argtypes = [ctypes.c_int]
    lib.clang_getBinaryOperatorKindSpelling.restype = ci._CXString
    text = lib.clang_getCString(lib.clang_getBinaryOperatorKindSpelling(lib.clang_getCursorBinaryOperatorKind(c)))
    return text.decode("utf-8") if isinstance(text, bytes) else text


def expr(c):
    k = c.kind
    kids = list(c.get_children())
    if k == CK.INTEGER_LITERAL:
        return "(Expr.lit %d)" % int(next(c.get_tokens()).spelling)
    if k in (CK.DECL_REF_EXPR, CK.MEMBER_REF_EXPR):
        return '(Expr.name "%s")' % c.spelling
    if k == CK.PAREN_EXPR:
        return "(Expr.paren %s)" % expr(kids[0])
    if k == CK.CXX_BOOL_LITERAL_EXPR:
        return "(Expr.truth %s)" % next(c.get_tokens()).spelling
    if k == CK.UNEXPOSED_EXPR and len(kids) == 1:       # what C++ does unasked: reading a name, or converting
        if kids[0].type.get_canonical().kind == TK.BOOL or c.type.get_canonical() == kids[0].type.get_canonical():
            return expr(kids[0])
        return "(Expr.conv Ty.%s %s)" % (ty(c.type, c), expr(kids[0]))
    if k == CK.BINARY_OPERATOR:
        op = operator(c)
        if op in BIN:
            return "(Expr.bin BinOp.%s %s %s)" % (BIN[op], expr(kids[0]), expr(kids[1]))
        if op in CMP:
            return "(Expr.cmp CmpOp.%s %s %s)" % (CMP[op], expr(kids[0]), expr(kids[1]))
    no(c, "an expression the spike does not copy: %s" % k.name)


def stmt(c, loops):
    """A statement as a tree. Each loop met is also put in `loops`, in the order the method is
    written in: its own lemma is made from it."""
    k = c.kind
    kids = list(c.get_children())
    if k == CK.COMPOUND_STMT:
        parts = [stmt(s, loops) for s in kids]
        inner = "Stmt.skip"
        for i, text in reversed(list(enumerate(parts))):
            inner = text if i == len(parts) - 1 else "(Stmt.seq %s %s)" % (text, inner)
        return "(Stmt.block %s)" % inner
    if k == CK.IF_STMT:
        return "(Stmt.ite %s %s %s %s)" % (expr(kids[0]), stmt(kids[1], loops), "true" if len(kids) > 2 else "false",
                                           stmt(kids[2], loops) if len(kids) > 2 else "Stmt.skip")
    if k == CK.DECL_STMT and len(kids) == 1 and kids[0].kind == CK.VAR_DECL:
        v = kids[0]
        first = [x for x in v.get_children() if x.kind != CK.TYPE_REF]
        if len(first) != 1:
            no(c, "a local with no first value")
        return '(Stmt.decl "%s" "%s" %s)' % (next(v.get_tokens()).spelling, v.spelling, expr(first[0]))
    if k == CK.FOR_STMT and len(kids) == 4 and kids[2].kind == CK.BINARY_OPERATOR and operator(kids[2]) == "=":
        here = {"kind": "for"}
        loops.append(here)          # before what is inside it: the order prooc.py numbers them in
        x, e = list(kids[2].get_children())
        here.update(init=stmt(kids[0], loops), c=expr(kids[1]), x=x.spelling, e=expr(e), body=stmt(kids[3], loops))
        return '(Stmt.forLoop %(init)s %(c)s "%(x)s" %(e)s %(body)s)' % here
    if k == CK.WHILE_STMT:
        here = {"kind": "while"}
        loops.append(here)
        here.update(c=expr(kids[0]), body=stmt(kids[1], loops))
        return "(Stmt.whileLoop %(c)s %(body)s)" % here
    if k == CK.RETURN_STMT:
        return "(Stmt.ret %s)" % ("(some %s)" % expr(kids[0]) if kids else "none")
    if k == CK.BINARY_OPERATOR and operator(c) == "=" and kids[0].kind in (CK.DECL_REF_EXPR, CK.MEMBER_REF_EXPR):
        return '(Stmt.set "%s" %s)' % (kids[0].spelling, expr(kids[1]))
    no(c, "a statement the spike does not copy: %s" % k.name)


VAL = {"BitVec 8": "u8", "BitVec 16": "u16", "BitVec 32": "u32", "BitVec 64": "u64"}


def loop_lemmas(n, m, number, loop, fields, model, result):
    """A loop's own lemmas. The tree's rounds are the model's, for any number of them: by
    induction on that number, each round compared as a method with no loop is. What the model's
    loop is given, and what it hands on from round to round, is read from the model's own text."""
    import re
    name = "%s_loop%d" % (m, number)
    head = re.search(r"^def %s\.loop%d \(fuel : Nat\) \(left : Nat\) \(me : %s\)((?: \(\w+ : BitVec \d+\))*) : " % (re.escape(m), number, n), model, re.M)
    onward = re.search(r"\| \.next \(?([\w, ]+)\)? => %s\.loop%d fuel left" % (re.escape(m), number), model)
    if not head or not onward:
        raise No("the model's loop %d of %s is not as this spike reads it" % (number, m))
    local = re.findall(r"\((\w+) : (BitVec \d+)\)", head.group(1))
    carried = [x.strip() for x in onward.group(1).split(",")]
    fb = "".join(" (%s : BitVec %d)" % (f, WIDTH[t]) for f, t in fields) + "".join(" (%s : %s)" % (x, t) for x, t in local)
    st = "⟨[%s], [%s]⟩" % (", ".join('("%s", some (Val.%s %s))' % (f, t, f) for f, t in fields),
                           ", ".join('("%s", some (Val.%s %s))' % (x, VAL[t], x) for x, t in local))
    after = "⟨%s, [%s]⟩" % ("store me'" if "me" in carried else "[%s]" % ", ".join('("%s", some (Val.%s %s))' % (f, t, f) for f, t in fields),
                            ", ".join('("%s", some (Val.%s %s%s))' % (x, VAL[t], x, "'" if x in carried else "") for x, t in local))
    pattern = "(%s)" % ", ".join(x + "'" for x in carried) if len(carried) > 1 else carried[0] + "'"
    whole = ("(Stmt.forLoop %(init)s %(c)s \"%(x)s\" %(e)s %(body)s)" if loop["kind"] == "for" else "(Stmt.whileLoop %(c)s %(body)s)") % loop
    round_ = ("Cxx.andThen (Cxx.exec fuel %(body)s s) (Cxx.assign \"%(x)s\" %(e)s)" if loop["kind"] == "for" else "Cxx.exec fuel %(body)s s") % loop
    going = "Cxx.iterate %s_cond (%s_round fuel) fuel" % (name, name)
    is_ = ("Cxx.leave s.locals.length (Cxx.andThen (Cxx.exec fuel %s s) (%s))" % (loop["init"], going) if loop["kind"] == "for"
           else "%s s" % going)
    return ["def %s_cond (s : St) : Option Bool := Cxx.cond %s s" % (name, loop["c"]), "",
            "def %s_round (fuel : Nat) (s : St) : Option Flow := %s" % (name, round_), "",
            "theorem %s_exec (fuel : Nat) (s : St) : Cxx.exec fuel %s s = %s := rfl" % (name, whole, is_), "",
            "theorem %s_agrees (fuel : Nat) : ∀ (left : Nat)%s," % (name, fb),
            "    Cxx.iterate %s_cond (%s_round fuel) left %s" % (name, name, st),
            "      = (%s.%s.loop%d fuel left ⟨%s⟩%s).map (fun r => match r with" % (n, m, number, ", ".join(f for f, _ in fields), "".join(" " + x for x, _ in local)),
            "          | .next %s | .done %s => Flow.go %s" % (pattern, pattern, after),
            "          | .ret p => Flow.back (store p.1) %s) := by" % result,
            "  intro left", "  induction left with",
            "  | zero => intros; simp [Cxx.iterate_zero, %s.%s.loop%d]" % (n, m, number),
            "  | succ left ih =>", "    intros",
            "    rw [Cxx.iterate_succ, %s.%s.loop%d]" % (n, m, number),
            "    cxx_agree [%s_cond, %s_round, %s.%s.round%d, %s.store, ih]" % (name, name, n, m, number, n),
            "    first | done | (split <;> split <;> first | rfl | (exfalso; bv_omega))", ""], \
        "%s.%s_exec, %s.%s_agrees" % (n, name, n, name), \
        ["  first", "  | done",
         "  | (generalize %s.%s.loop%d fuel fuel%s = r" % (n, m, number, " _" * (1 + len(local))),
         "     cases r with",
         "     | none => simp [Cxx.leave_none, Cxx.finish_none, Cxx.andThen_none]",
         "     | some st => cases st <;> cxx_agree [%s.store])" % n]


def words(c):
    return ", ".join('"%s"' % t.spelling for t in c.get_tokens() if t.kind != TokenKind.COMMENT)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("source")
    ap.add_argument("-o", "--out", default="gen")
    args = ap.parse_args()
    configure_libclang()
    builtin = probe([os.environ.get("CC", "cc"), "-print-resource-dir"], "-resource-dir") \
        or probe([os.environ.get("CC", "cc"), "-print-file-name=include"], "-isystem")
    tu = ci.Index.create().parse(args.source, args=["-x", "c++", "-std=c++20", "-Wno-pragma-once-outside-header"] + builtin)
    if [d for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]:
        sys.exit("tree: the source does not compile")
    here = os.path.abspath(args.source)
    klass = [c for c in tu.cursor.get_children() if c.kind == CK.CLASS_DECL and c.is_definition()
             and c.location.file and os.path.abspath(c.location.file.name) == here]
    if len(klass) != 1:
        sys.exit("tree: one class is wanted")
    k = klass[0]
    n = k.spelling
    fields = [(c.spelling, ty(c.type, c)) for c in k.get_children() if c.kind == CK.FIELD_DECL]
    model = open(os.path.join(args.out, n + "Model.lean")).read()      # prooc.py's, already written: a loop's shape is read from it
    L = ["import Cxx", "import %sModel" % n, "", "open Cxx", "",
         "set_option linter.unusedSimpArgs false", "",
         "/-! GENERATED by prover/spike-tree/tree.py from %s. Do not edit." % os.path.basename(args.source),
         "Each method of %s as a tree of its own words; that the tree is those words (`_text`); and that" % n,
         "what Cxx.lean says the tree means is the model prooc.py wrote (`_agrees`). -/", "",
         "namespace %s" % n, "",
         "/-- The object, as names and what they hold. -/",
         "def store (me : %s) : Cxx.Store := [%s]" % (n, ", ".join('("%s", some (Val.%s me.%s))' % (f, t, f) for f, t in fields)), "",
         "/-- The object before its constructor has run: each field declared, none given a value. -/",
         "def blank : Cxx.Store := [%s]" % ", ".join('("%s", none)' % f for f, _ in fields), ""]
    for c in k.get_children():
        body = [x for x in c.get_children() if x.kind == CK.COMPOUND_STMT]
        if c.kind not in (CK.CONSTRUCTOR, CK.CXX_METHOD) or not body:
            continue
        m = "new" if c.kind == CK.CONSTRUCTOR else c.spelling
        params = [(p.spelling, ty(p.type, p)) for p in c.get_children() if p.kind == CK.PARM_DECL]
        void = c.kind == CK.CONSTRUCTOR or c.result_type.get_canonical().kind == TK.VOID
        binders = "".join(" (%s : BitVec %d)" % (p, WIDTH[t]) for p, t in params)
        given = "[%s]" % ", ".join('("%s", some (Val.%s %s))' % (p, t, p) for p, t in params)
        loops = []
        tree = stmt(body[0], loops)
        result = "none" if void or m == "invariant" else "(some (Val.%s p.2))" % ty(c.result_type, c)
        uses, after = "", []
        fuel = " fuel" if loops else ""
        L += ["def tree_%s : Cxx.Method := ⟨%s, %s⟩" % (m, "true" if void else "false", tree), "",
              "theorem %s_text : tree_%s.body.tokens = [%s] := by" % (m, m, words(body[0])),
              "  rfl", ""]
        for number, loop in enumerate(loops, 1):
            lemmas, names, finish = loop_lemmas(n, m, number, loop, fields, model, result)
            L += lemmas
            uses += ", " + names
            after = finish
        names = "%s.tree_%s, %s.store, %s.blank, %s.%s%s" % (n, m, n, n, n, "Inv" if m == "invariant" else m, uses)
        if m == "invariant":        # a condition on the fields: what it returns is what Inv says
            L += ["theorem invariant_agrees (me : %s) :" % n,
                  "    Cxx.call tree_invariant 0 (store me) [] = none ∧",
                  "    (match tree_invariant.body with",
                  "     | Stmt.block (Stmt.ret (some e)) => Cxx.cond e ⟨store me, []⟩ = some (decide (%s.Inv me))" % n,
                  "     | _ => False) := by",
                  "  constructor <;> cxx_agree [%s]" % names, ""]
        elif m == "new":
            L += ["theorem new_agrees : Cxx.call tree_new 0 blank [] = %s.new.map (fun me => (store me, none)) := by" % n,
                  "  cxx_agree [%s, %s.raw]" % (names, n), ""]
        else:
            L += ["theorem %s_agrees (fuel : Nat) (me : %s)%s :" % (m, n, binders),
                  "    Cxx.call tree_%s fuel (store me) %s = (%s.%s%s me%s).map (fun p => (store p.1, %s)) := by"
                  % (m, given, n, m, fuel, "".join(" " + p for p, _ in params), result),
                  "  cases me",
                  "  cxx_agree [%s]" % names] + after + [""]
    L += ["end %s" % n]
    os.makedirs(args.out, exist_ok=True)
    path = os.path.join(args.out, n + "Tree.lean")
    open(path, "w").write("\n".join(L) + "\n")
    print("tree: %s" % path)


if __name__ == "__main__":
    try:
        main()
    except No as e:
        sys.exit("tree: refused\n  %s" % e)
