#!/usr/bin/env python3
"""
tree -- a SPIKE (2026-11-18): copy a class's methods out of the compiler's reading as trees, for
Cxx.lean, and ask the kernel two things of each.

    python3 spike-tree/tree.py model/Gauge.hpp -o gen        writes gen/GaugeTree.lean

The tree is the generator's own: what reader.py read of the class (reader.read, the cxx.Klass that
prooc.py writes the model from), written as Cxx.lean's tree. Nothing here asks the compiler of the
methods but what the reader keeps for this: each body's words.

For each method (and the constructor, and the invariant) it writes:
  C.tree_M     the method's body as a Cxx.Stmt: its words, in the shape the compiler read them in
  C.M_text     that the tree, written back as words, is the method's body word for word: so the
               reader read rightly, and this copied rightly. The words on the right are the
               compiler's own tokens of the source (cxx.Method.words); nothing here chose them
  C.M_agrees   that what Cxx.lean says the tree means is the model prooc.py wrote: so the model,
               and every proof about it, is about the meaning said there, once

This program says nothing of what C++ means. It gives no meaning to an operator, and resolves no
name: `level` is the word "level", and Cxx.lean says what a word stands for. The one thing it writes
that has no word in the source is a conversion C++ makes unasked (`level = 0`: an int to a
uint32_t), which the reader took from the compiler's tree. A class with anything Cxx.lean does not
say is refused, saying what.
"""
import argparse
import os
import sys

import clang.cindex as ci

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from clang_edge import configure_libclang, probe, Unsupported   # noqa: E402
from cxxtypes import READ, Int   # noqa: E402
import reader   # noqa: E402
from subject import PRE_FLAGS, file_scope, with_pre   # noqa: E402
from cxx import (Bin, Block, Cmp, Conv, Decl, ForLoop, Ite, Lit, Name, Paren, Ret, Set,   # noqa: E402
                 Truth, Value, WhileLoop)

WIDTH = {"u8": 8, "u16": 16, "u32": 32, "u64": 64}
BIN = {"+": "add", "-": "sub", "*": "mul", "&": "and", "|": "or", "^": "xor"}
CMP = {"<": "lt", "<=": "le", ">": "gt", ">=": "ge", "==": "eq", "!=": "ne"}


class No(Exception):
    pass


def no(node, why):
    raise No("%s: %s" % (getattr(node, "place", "") or "?", why))


def ty(t, at):
    """Cxx.lean's name of a type (an Int of the tree)."""
    if not isinstance(t, Int) or t.is_bool or (t.signed and t.width != 32):
        no(at, "a type the spike does not copy: %s" % (
            "bool" if isinstance(t, Int) and t.is_bool else type(t).__name__ if not isinstance(t, Int) else "a signed %d-bit number" % t.width))
    return "int" if t.signed else "u%d" % t.width


def expr(e):
    if isinstance(e, Lit):
        if e.written is None or not e.written.isdigit():
            no(e, "a number the spike does not copy: a name for one, one converted by a cast, or a literal not in decimal")
        lit = "(Expr.lit %d)" % int(e.written)
        return lit if e.converted is None else "(Expr.conv Ty.%s %s)" % (ty(e.converted, e), lit)
    if isinstance(e, Name):
        if e.what not in ("local", "param", "field"):
            no(e, "a name the spike does not copy (a value of another class, or of a template)")
        return '(Expr.name "%s")' % e.x
    if isinstance(e, Paren):
        return "(Expr.paren %s)" % expr(e.e)
    if isinstance(e, Truth):
        return "(Expr.truth %s)" % ("true" if e.value else "false")
    if isinstance(e, Conv):        # what C++ does unasked: reading a name, or converting
        if e.cast:
            no(e, "a cast: the spike copies only the conversions C++ makes unasked")
        if e.src.is_bool or e.same:
            return expr(e.e)
        return "(Expr.conv Ty.%s %s)" % (ty(e.dst, e), expr(e.e))
    if isinstance(e, Bin) and e.op in BIN:
        return "(Expr.bin BinOp.%s %s %s)" % (BIN[e.op], expr(e.a), expr(e.b))
    if isinstance(e, Value) and isinstance(e.c, Cmp):     # a comparison as a number (`return a <= b;`)
        return expr(e.c)
    if isinstance(e, Cmp):
        return "(Expr.cmp CmpOp.%s %s %s)" % (CMP[e.op], expr(e.a), expr(e.b))
    no(e, "an expression the spike does not copy: %s" % type(e).__name__)


def cond(c):
    """A condition, where Cxx.lean's tree has an Expr: of `if`, `while`, `for`, the invariant's return."""
    if not isinstance(c, (Cmp, Truth)):
        no(c, "a condition the spike does not copy: %s" % type(c).__name__)
    text = expr(c)
    for _ in range(c.parens):
        text = "(Expr.paren %s)" % text
    return text


def stmt(s, loops):
    """A statement as a tree. Each loop met is also put in `loops`, in the order the method is
    written in: its own lemma is made from it."""
    if isinstance(s, Block):
        parts = [stmt(x, loops) for x in s.stmts]
        inner = "Stmt.skip"
        for i, text in reversed(list(enumerate(parts))):
            inner = text if i == len(parts) - 1 else "(Stmt.seq %s %s)" % (text, inner)
        return "(Stmt.block %s)" % inner
    if isinstance(s, Ite):
        return "(Stmt.ite %s %s %s %s)" % (cond(s.c), stmt(s.then, loops), "true" if s.other is not None else "false",
                                           stmt(s.other, loops) if s.other is not None else "Stmt.skip")
    if isinstance(s, Decl):
        return '(Stmt.decl "%s" "%s" %s)' % (s.word, s.x, expr(s.value))
    if isinstance(s, ForLoop) and s.init is not None and isinstance(s.inc, Set) and isinstance(s.inc.target, Name):
        here = {"kind": "for"}
        loops.append(here)          # before what is inside it: the order prooc.py numbers them in
        here.update(init=stmt(s.init, loops), c=cond(s.c), x=s.inc.target.x, e=expr(s.inc.value), body=stmt(s.body, loops))
        return '(Stmt.forLoop %(init)s %(c)s "%(x)s" %(e)s %(body)s)' % here
    if isinstance(s, WhileLoop):
        here = {"kind": "while"}
        loops.append(here)
        here.update(c=cond(s.c), body=stmt(s.body, loops))
        return "(Stmt.whileLoop %(c)s %(body)s)" % here
    if isinstance(s, Ret):
        return "(Stmt.ret %s)" % ("(some %s)" % expr(s.value) if s.value is not None else "none")
    if isinstance(s, Set) and isinstance(s.target, Name):
        return '(Stmt.set "%s" %s)' % (s.target.x, expr(s.value))
    no(s, "a statement the spike does not copy: %s" % type(s).__name__)


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


def words(ws):
    return ", ".join('"%s"' % w for w in ws)


def read_class(source):
    """The one class of the file, as the generator reads it (prooc.py, for a file of its own)."""
    configure_libclang()
    index = ci.Index.create()
    builtin = probe([os.environ.get("CC", "cc"), "-print-resource-dir"], "-resource-dir") \
        or probe([os.environ.get("CC", "cc"), "-print-file-name=include"], "-isystem")
    here = os.path.abspath(source)
    flags = ["-x", "c++", "-std=c++20", "-Wno-pragma-once-outside-header",
             "-I" + os.path.dirname(here),
             "-I" + os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "model")] + builtin
    text = open(source, encoding="utf-8").read()
    read = with_pre(index, here, text, flags)
    READ["text"] = (read or text).encode("utf-8")
    tu = index.parse(here, args=flags + PRE_FLAGS, unsaved_files=[(here, read or text)])
    if [d for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]:
        sys.exit("tree: the source does not compile")
    classes = file_scope(tu.cursor, here, False)
    if len(classes) != 1:
        sys.exit("tree: one class is wanted")
    return reader.read(classes[0])


def at(place):
    """Where a place is in the file, to put what was read in the order of the text."""
    _, line, column = place.rsplit(":", 2)
    return int(line), int(column)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("source")
    ap.add_argument("-o", "--out", default="gen")
    args = ap.parse_args()
    k = read_class(args.source)
    n = k.name
    if k.is_function or k.generic or k.inits or k.ctor_params or k.ctor_pre or k.ctor_tested or k.inv is None:
        no(k, "a function, a class template, an initializer list, a constructor that takes something or "
              "expects something, or no invariant: the spike copies none of these")
    for f in k.fields:
        if f.count is not None:
            no(k, "the field '%s' is an array: the spike does not copy one" % f.name)
    fields = [(f.name, ty(f.type, k)) for f in k.fields]
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
    # (name, its parameters, void, its result's type, its body as a tree's Stmt is made of, its words), in the order of the text
    each = [(at(k.ctor_body.place), "new", [], True, None, k.ctor_body, k.ctor_words),
            (at(k.inv.place), "invariant", [], False, None, None, k.inv_words)]
    for m in k.methods:
        if m.pre or m.tested or m.lengths:
            no(m, "'%s' expects something of its caller, or takes a view: the spike copies neither" % m.name)
        each.append((at(m.place), m.name, m.params, m.result is None, m.result, m.body, m.words))
    for _, m, params, void, rt, body, ws in sorted(each, key=lambda x: x[0]):
        params = [(p, ty(t, k)) for p, t in params]
        binders = "".join(" (%s : BitVec %d)" % (p, WIDTH[t]) for p, t in params)
        given = "[%s]" % ", ".join('("%s", some (Val.%s %s))' % (p, t, p) for p, t in params)
        loops = []
        tree = "(Stmt.block (Stmt.ret (some %s)))" % cond(k.inv) if m == "invariant" else stmt(body, loops)
        result = "none" if void or m == "invariant" else "(some (Val.%s p.2))" % ty(rt, k)
        uses, after = "", []
        fuel = " fuel" if loops else ""
        L += ["def tree_%s : Cxx.Method := ⟨%s, %s⟩" % (m, "true" if void else "false", tree), "",
              "theorem %s_text : tree_%s.body.tokens = [%s] := by" % (m, m, words(ws)),
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
    except Unsupported as e:
        sys.exit("tree: refused: the generator does not read it\n  %s" % e)
