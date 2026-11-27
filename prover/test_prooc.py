#!/usr/bin/env python3
"""
The generator's own suite: each case is a way a class could be wrong, and the tool must say so.

  refusals   a boundary that leaks, or C++ with no exact meaning here: prooc.py exits 2
  red        the class changed so that what is owed is false, or the model wrong; or the claims
             made to cheat, as a claims file nobody trusts might: prove.sh fails, at the step named

Usage: LEAN=/path/to/lean python3 prover/test_prooc.py     (seen red 2026-11-18; about 3 minutes)
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.environ.get("LEAN", "lean")
failures = []


def check(name, ok, more=""):
    print("%-78s %s" % (name, "ok" if ok else "FAIL " + more))
    if not ok:
        failures.append(name)


INV = "  bool invariant() const { return true; }"


def gauge(fields="private:\n  uint32_t level;\n  uint32_t limit;", extra="", ctor="level = 0; limit = 1;", inv=INV):
    return """#pragma once
#include <cstdint>
class Gauge {
public:
  Gauge() { %s }
  uint32_t get() const { return level; }
%s
%s
%s
};
""" % (ctor, inv, extra, fields)


REFUSED = [
    ("a public field", gauge(fields="public:\n  uint32_t level;\n  uint32_t limit;"), "not private"),
    ("a protected field", gauge(fields="protected:\n  uint32_t level;\n  uint32_t limit;"), "not private"),
    ("a friend", gauge(extra="  friend class Other;"), "friend"),
    ("a method that returns a pointer to a field", gauge(extra="  uint32_t *where() { return &level; }"), "not one the model knows"),
    ("a method that returns a reference to a field", gauge(extra="  uint32_t &where() { return level; }"), "not one the model knows"),
    ("a pointer parameter that is not to bytes", gauge(extra="  void from(const uint32_t *p, unsigned long n) { level = 0; }"), "not to const bytes"),
    ("a pointer to bytes with no length after it", gauge(extra="  void from(const unsigned char *p) { level = 0; }"), "with their number"),
    ("a pointer to bytes that may be written", gauge(extra="  void from(unsigned char *p, unsigned long n) { level = 0; }"), "not to const bytes"),
    ("a view's length assigned", gauge(extra="  void from(const unsigned char *p, unsigned long n) { n = 0; level = 0; }"), "an assignment to a view's length"),
    ("signed bytes read as they are", gauge(extra="  void from(const char *p, unsigned long n) { if (n > 0) level = p[0]; }"), "the type 'char' is not one the model knows"),
    ("a view's pointer moved", gauge(extra="  void from(const unsigned char *p, unsigned long n) { const unsigned char *q = p + 1; if (n > 1) level = q[0]; }"), "made once from a view's own pointer"),
    ("the address of a field, used", gauge(extra="  uint32_t odd() { return *(&level); }"), "operator"),
    ("a base class", "#pragma once\n#include <cstdint>\nclass B { public: B() {} bool invariant() const { return true; } };\nclass D : public B { public: D() { x = 0; } private: uint32_t x; };\n", "base class"),
    ("a global beside the class", gauge() + "uint32_t shared;\n", "at file scope"),
    ("a field the constructor does not assign", gauge(ctor="level = 0;"), "does not assign limit"),
    ("a field read in the constructor", gauge(ctor="level = 0; limit = level;"), "read in the constructor"),
    ("a local with no first value", gauge(extra="  uint32_t f() { uint32_t x; return x; }"), "no first value"),
    ("signed arithmetic", gauge(extra="  uint32_t f(uint8_t a) { return a + 1; }"), "can overflow"),
    ("a signed field", gauge(fields="private:\n  uint32_t level;\n  int limit;"), "signed field"),
    ("a do-while", gauge(extra="  void f() { do { level = level - 1; } while (level > 0); }"), "not in the spike's subset"),
    ("a for with a part left out", gauge(extra="  void f() { for (; level > 0;) level = level - 1; }"), "a part left out"),
    ("a shift by a signed amount", gauge(extra="  uint32_t f(uint8_t n) { return level << n; }"), "a shift by a signed amount"),
    ("a shift in the invariant by an amount that is not a literal", gauge(inv="  bool invariant() const { return (level >> limit) == 0; }"), "a shift in the invariant"),
    ("a name declared twice in one method", gauge(extra="  uint32_t f() { uint32_t x = 1; if (level > 0) { uint32_t x = 2; return x; } return x; }"), "declared twice"),
    ("a view kept in a field", "#pragma once\n#include <cstdint>\n#include \"Bytes.hpp\"\nclass A { public: A() : kept(0, 0) { n = 0; }\n  void f(Bytes d) { n = d.size(); }\nprivate: uint64_t n; Bytes kept; };\n", "not one the model knows"),
    ("a view handed to something else", "#pragma once\n#include <cstdint>\n#include \"Bytes.hpp\"\nuint64_t other(Bytes d);\nclass A { public: A() { n = 0; }\n  void f(Bytes d) { n = other(d); }\nprivate: uint64_t n; };\n", "at file scope"),
    ("a call to a method written later", gauge(extra="  uint32_t f() { return later(); }\n  uint32_t later() const { return level; }"), "not written before this method"),
    ("a call inside an expression to a method that changes the object", gauge(extra="  uint32_t bump() { level = level + 1; return level; }\n  uint32_t f() { return bump() + 1; }"), "make the call a statement"),
    ("a parameter of another class, changed", "#pragma once\n#include <cstdint>\nclass P { public: P() { v = 0; } void bump() { v = v + 1; } bool invariant() const { return true; } private: uint32_t v; };\nclass A { public: A() { n = 0; } void f(P p) { p.bump(); n = 0; } bool invariant() const { return true; } private: uint32_t n; };\n", "call expr"),
    ("a parameter of a type that is no class read here", "#pragma once\n#include <cstdint>\nstruct S { int x; };\nclass A { public: A() { n = 0; } void f(S s) { n = 0; } bool invariant() const { return true; } private: uint32_t n; };\n", "at file scope"),
    ("a static member that is not const", gauge(extra="  static uint32_t shared;"), "state outside the object"),
    ("a memset of part of an array", "#pragma once\n#include <cstdint>\n#include <cstring>\nclass A { public: A() { v[0] = 0; v[1] = 0; }\n  void f() { memset(v, 0, 4); }\n  bool invariant() const { return true; }\nprivate: uint32_t v[2]; };\n", "memset( FIELD, BYTE, sizeof( FIELD ) )"),
    ("a virtual method", gauge(extra="  virtual void f() { level = 0; }"), "virtual"),
    ("a mutable field", gauge(fields="private:\n  mutable uint32_t level;\n  uint32_t limit;"), "mutable"),
    ("a signed division", gauge(extra="  uint32_t f(uint8_t a) { return a / 2; }"), "'/' on signed numbers"),
    ("a class that does not say its invariant", gauge(inv=""), "no `bool invariant() const`"),
    ("an invariant that is not const", gauge(inv="  bool invariant() { return true; }"), "the invariant is"),
    ("an invariant that does more than return a condition", gauge(inv="  bool invariant() const { if (level > 0) return true; return false; }"), "one `return`"),
    ("an invariant that names an element outside the array", "#pragma once\n#include <cstdint>\nclass A { public: A() { v[0] = 0; v[1] = 0; }\n  bool invariant() const { return v[2] == 0; }\nprivate: uint32_t v[2]; };\n", "inside the array"),
    ("a precondition that reads an array", "#pragma once\n#include <cstdint>\nclass A { public: A() { v[0] = 0; v[1] = 0; }\n  uint32_t f(uint32_t i) const pre( v[i] == 0 ) { return i; }\n  bool invariant() const { return true; }\nprivate: uint32_t v[2]; };\n", "an element by a number inside the array"),
    ("a constructor's precondition that reads a field (it is not yet given a value)", "#pragma once\n#include <cstdint>\nclass A { public: A( uint32_t n ) pre( n < v ) { v = n; }\n  bool invariant() const { return true; }\nprivate: uint32_t v; };\n", "constructor"),
    ("the generator's own name for a precondition, written in the class", gauge(extra="  void f() { prooc_pre( level == 0 ); }"), "the generator's own"),
    ("a class template that compares its type's values other than by <=", "#pragma once\ntemplate <typename T, T A, T B> class G { public: G( T n ) : v( n ) {}\n\n  bool invariant() const { return A < v; }\nprivate: T v; };\n", "compared by `<=`, and no other way"),
    ("a class template that adds two of its type's values", "#pragma once\ntemplate <typename T, T A, T B> class G { public: G( T n ) : v( n ) {}\n  T twice() const { return v + v; }\n  bool invariant() const { return A <= v; }\nprivate: T v; };\n", "'<dependent type>' is not one the model knows"),
    ("a class template with a loop", "#pragma once\ntemplate <typename T, T A, T B> class G { public: G( T n ) : v( n ) {}\n  void f() { while ( A <= v ) { } }\n  bool invariant() const { return true; }\nprivate: T v; };\n", "a loop in a class template"),
    ("a class template of two types", "#pragma once\ntemplate <typename T, typename U> class G { public: G( T n ) : v( n ) {}\n  bool invariant() const { return true; }\nprivate: T v; };\n", "not of one type and values of that type"),
    ("a proved method that is not a way in calls a _checked one", gauge(extra="  void set_checked( uint32_t n ) { if ( n <= limit ) { level = n; } }\n  void fill() { set_checked( limit ); }"), "which is not a `_checked` way in"),
    ("a proved method that is not a way in takes a _checked value", "#pragma once\n#include <cstdint>\nclass N_checked { public: N_checked( uint32_t n ) : v( n ) {}\n  uint32_t number() const { return v; }\n  bool invariant() const { return true; }\nprivate: uint32_t v; };\nclass A { public: A() : v( 0 ) {}\n  void set( N_checked n ) { v = n.number(); }\n  bool invariant() const { return true; }\nprivate: uint32_t v; };\n", "which is not a `_checked` way in"),
    ("a thrown value made of the state: what is thrown is not read", "#pragma once\n#include <cstdint>\n#include <stdexcept>\n#include <string>\nclass A { public: A() { n = 0; }\n  void f() { if ( n > 0 ) throw std::length_error( std::to_string( n ) ); }\n  bool invariant() const { return true; }\nprivate: uint32_t n; };\n", "a thrown value made of more than literals"),
    ("a throw of a number", "#pragma once\n#include <cstdint>\nclass A { public: A() { n = 0; }\n  void f() { if ( n > 0 ) throw 1; }\n  bool invariant() const { return true; }\nprivate: uint32_t n; };\n", "not of a value of a class"),
    ("a call of a method that may throw", "#pragma once\n#include <cstdint>\n#include <stdexcept>\nclass A { public: A() { n = 0; }\n  void f() { if ( n > 0 ) throw std::logic_error( \"no\" ); }\n  void g() { f(); }\n  bool invariant() const { return true; }\nprivate: uint32_t n; };\n", "which may throw"),
    ("an assert compiled away (NDEBUG): what follows may not rest on it", "#pragma once\n#define NDEBUG\n#include <cassert>\n#include <cstdint>\nclass A { public: A() { n = 0; }\n  uint32_t f() { assert( n == 0 ); return n; }\n  bool invariant() const { return true; }\nprivate: uint32_t n; };\n", "an assert compiled away"),
    ("an end of the process given the state", "#pragma once\n#include <cstdint>\n#include <cstdlib>\nclass A { public: A() { n = 0; }\n  void f() { if ( n > 0 ) exit( n ); }\n  bool invariant() const { return true; }\nprivate: uint32_t n; };\n", "given more than literals"),
    ("a call of the system's that is not just before an end", "#pragma once\n#include <cstdint>\n#include <cstdio>\nclass A { public: A() { n = 0; }\n  void f() { fprintf( stderr, \"no\\n\" ); n = 1; }\n  bool invariant() const { return true; }\nprivate: uint32_t n; };\n", "not in the spike's subset"),
    ("a product of two signed numbers (not yet: only + and - are read)", "#pragma once\n#include <cstdint>\nclass A { public: A() { n = 0; }\n  uint32_t f( uint32_t m ) { int x = m; int y = x * 2; n = (uint32_t)y; return n; }\n  bool invariant() const { return true; }\nprivate: uint32_t n; };\n", "can overflow"),
    ("a signed index", "#pragma once\n#include <cstdint>\nclass A { public: A() { v[0] = 0; v[1] = 0; }\n  uint32_t at(uint8_t i) const { return v[i & 1]; }\n  bool invariant() const { return true; }\nprivate: uint32_t v[2]; };\n", "signed type"),
]


def refusals():
    for name, source, expect in REFUSED:
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "Gauge.hpp")
            open(path, "w").write(source)
            shutil.copy(os.path.join(HERE, "model", "Bytes.hpp"), d)
            r = subprocess.run([sys.executable, os.path.join(HERE, "prooc.py"), path, "-o", os.path.join(d, "gen")],
                               capture_output=True, text=True)
            wrote = os.path.exists(os.path.join(d, "gen"))
            check("refused: " + name, r.returncode == 2 and expect in r.stderr and not wrote,
                  "(exit %d) %s" % (r.returncode, r.stderr.strip()[-200:]))


def prove(edit, klass):
    """A copy of this directory with `edit(dir)` applied, then prove.sh: (exit code, output)."""
    with tempfile.TemporaryDirectory() as d:
        work = os.path.join(d, "w")
        shutil.copytree(HERE, work, ignore=shutil.ignore_patterns("build", "gen", "__pycache__"))
        edit(work)
        r = subprocess.run(["sh", os.path.join(work, "prove.sh")] + klass.split(), capture_output=True, text=True,
                           env=dict(os.environ, LEAN=LEAN, PYTHON=sys.executable, SUBJECT=os.path.join(work, "sample")))
        return r.returncode, r.stdout + r.stderr


def ingress(edit):
    """As prove(), for the sample's classes about bounded numbers, then ingress.py: the rule
    between code that is proved and code that is not."""
    names = "bounded_of bounded_checked_of Tank".split()
    with tempfile.TemporaryDirectory() as d:
        work = os.path.join(d, "w")
        shutil.copytree(HERE, work, ignore=shutil.ignore_patterns("build", "gen", "__pycache__"))
        shutil.rmtree(os.path.join(work, "sample", "stats"))      # the other samples' classes are not proved here
        edit(work)
        env = dict(os.environ, LEAN=LEAN, PYTHON=sys.executable, SUBJECT=os.path.join(work, "sample"), STRONG="strong")
        r = subprocess.run(["sh", os.path.join(work, "prove.sh")] + names, capture_output=True, text=True, env=env)
        if r.returncode:
            return r.returncode, r.stdout + r.stderr
        r = subprocess.run([sys.executable, os.path.join(work, "ingress.py")] + names, capture_output=True, text=True, env=env)
        return r.returncode, r.stdout + r.stderr


def replace(rel, old, new):
    def edit(work):
        path = os.path.join(work, rel)
        text = open(path).read()
        assert text.count(old) == 1, (rel, old)
        open(path, "w").write(text.replace(old, new))
    return edit


def model_wrong(work):
    """The generator made to translate a returned literal wrongly: no claim is false of the model,
    but it is not the C++."""
    replace("model.py", 'out.append(pad + self.say_return(self.expr(s.value) if s.value is not None else "()"))',
            'out.append(pad + self.say_return(("1#32" if isinstance(s.value, Lit) else self.expr(s.value)) if s.value is not None else "()"))')(work)


OWED = """/-- Everything owed. -/
theorem owed : Gauge.Owed :=
  { new_safe, new_inv, get_safe, get_same, getLimit_safe, getLimit_same, set_safe, set_inv,
    setLimit_safe, setLimit_inv }
"""


def kernel_off(work):
    """A theorem named `owed`, of the right statement, whose proof is no proof of it, added with
    Lean's kernel told not to look. Only asking the kernel again finds it."""
    replace("claims/GaugeClaims.lean", "import GaugeOwed\n", "import GaugeOwed\nimport Lean\n")(work)
    replace("claims/GaugeClaims.lean", OWED, """open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl (.thmDecl
  { name := `Gauge.Claims.owed, levelParams := [], type := mkConst `Gauge.Owed, value := mkConst ``True.intro })
""")(work)


RED = [
    ("as it is: proved", "Gauge", lambda work: None, 0, "PROVED Gauge"),
    ("as it is: proved", "Tally", lambda work: None, 0, "PROVED Tally"),
    ("as it is: proved, a method that throws among them", "Ration", lambda work: None, 0, "PROVED Ration"),
    ("the C++ changes what was taken before it throws: the state the throw leaves breaks the invariant, and its proof fails", "Ration",
     replace("model/Ration.hpp", "    if ( n > stock ) {\n      throw std::length_error( \"not that much left\" );\n    }\n    stock = stock - n;\n    taken = taken + n;",
             "    taken = taken + n;\n    if ( n > stock ) {\n      throw std::length_error( \"not that much left\" );\n    }\n    stock = stock - n;"), 1, "RationClaims.lean"),
    ("as it is: proved, a method that ends the process among them", "Fuse", lambda work: None, 0, "PROVED Fuse"),
    ("the C++ ends the process a blow later: the count passes 3 first, and the invariant's proof fails", "Fuse",
     replace("model/Fuse.hpp", "if ( blows == 3 ) {", "if ( blows == 4 ) {"), 1, "FuseClaims.lean"),
    ("as it is: proved, a subtraction of two ints among them", "Frame", lambda work: None, 0, "PROVED Frame"),
    ("the C++ drops its upper bound: an n near 2^31 makes the int subtraction overflow, and the safety proof fails", "Frame",
     replace("model/Frame.hpp", "if ( n < 24 || n > 65536 ) {", "if ( n < 24 ) {"), 1, "FrameClaims.lean"),
    ("the C++ loses a clamp: the invariant's proof fails", "Gauge",
     replace("model/Gauge.hpp", "if (level > value) level = value;", ""), 1, "GaugeClaims.lean"),
    ("as it is: what its proof file claims is proved too", "Gauge", lambda work: None, 0, "PROVED Gauge, as proofs/Gauge.proof.cpp says it"),
    ("a PROVE of the proof file claims more than is so (below the limit, not at most it): it is not proved", "Gauge",
     replace("proofs/Gauge.proof.cpp", "PROVE( gauge.get() <= limit );", "PROVE( gauge.get() < limit );"), 1, "a PROVE of proofs/Gauge.proof.cpp is not proved"),
    ("the proof file no longer says what a round hands to the next: the loop is not proved", "Gauge",
     replace("proofs/Gauge.proof.cpp", "      PROVE( gauge.getLimit() == limit ); /* (setting the level leaves the limit: the next round rests on it) */\n", ""),
     1, "a PROVE of proofs/Gauge.proof.cpp is not proved"),
    ("the proof file calls what the class has not: it does not compile", "Gauge",
     replace("proofs/Gauge.proof.cpp", "gauge.setLimit( lower );", "gauge.setCeiling( lower );"), 1, "proofs/Gauge.proof.cpp does not compile"),
    ("the proof file has a statement the reader does not know: refused, not guessed", "Gauge",
     replace("proofs/Gauge.proof.cpp", "gauge.setLimit( lower );", "gauge.setLimit( lower ); if ( lower > 3 ) gauge.set( 3 );"), 1, "proofs/Gauge.proof.cpp is not read"),
    ("the loop around no longer bounds the limit: what the loop inside rested on is gone, and it is not proved", "Gauge",
     replace("proofs/Gauge.proof.cpp", "all<uint32_t>( 0, 1000 )", "all<uint32_t>()"), 1, "a PROVE of proofs/Gauge.proof.cpp is not proved"),
    ("the C++ indexes with three bits: the safety proof fails", "Tally",
     replace("model/Tally.hpp", "byte & 3", "byte & 7"), 1, "TallyClaims.lean"),
    ("the C++ drops a bounds test: the safety proof fails", "Tally",
     replace("model/Tally.hpp", "if (kind >= 4) return 0;", ""), 1, "TallyClaims.lean"),
    ("a proof replaced by sorry: found", "Gauge",
     replace("claims/GaugeClaims.lean", "  intro me value _; simp [Gauge.set]; split <;> simp", "  sorry"), 1, "the audit refused"),
    ("a claim removed: the proof of what is owed does not compile", "Gauge",
     replace("claims/GaugeClaims.lean", "theorem getLimit_safe", "theorem getLimit_safe_renamed"), 1, "a proof does not hold"),
    ("a claim proved of something weaker: the proof of what is owed does not compile", "Gauge",
     replace("claims/GaugeClaims.lean", "theorem set_safe : ∀ (me : Gauge) (value : BitVec 32), Inv me → (Gauge.set me value).isSome := by\n  intro me value _; simp [Gauge.set]; split <;> simp", "theorem set_safe : ∀ (me : Gauge), Inv me → (Gauge.set me 0#32).isSome := by\n  intro me _; simp [Gauge.set]"), 1, "a proof does not hold"),
    ("the claims take what is owed as an axiom of their own: the audit refuses", "Gauge",
     replace("claims/GaugeClaims.lean", OWED, "axiom cheat : Gauge.Owed\ntheorem owed : Gauge.Owed := cheat\n"), 1, "it rests on [Gauge.Claims.cheat]"),
    ("the claims prove a statement by compiled code, which they could have swapped: the audit refuses", "Gauge",
     replace("claims/GaugeClaims.lean", "theorem new_safe : Gauge.new.isSome := by\n  simp [Gauge.new]", "theorem new_safe : Gauge.new.isSome := by\n  native_decide"), 1, "the audit refused"),
    ("the claims' `owed` is a proof of something else: the audit refuses", "Gauge",
     replace("claims/GaugeClaims.lean", OWED, "theorem owed : True := trivial\n"), 1, "is not a proof of `Gauge.Owed`"),
    ("the claims have no `owed`: the audit refuses", "Gauge",
     replace("claims/GaugeClaims.lean", OWED, ""), 1, "the claims do not have"),
    ("the claims put in a false proof with the kernel switched off: the kernel, asked again, refuses", "Gauge",
     kernel_off, 1, "Lean's kernel, asked again, does not accept"),
    ("the claims write over what is owed while they are checked: found", "Gauge",
     replace("claims/GaugeClaims.lean", "namespace Gauge\n", "#eval (do IO.FS.writeFile \"build/other\" \"\"; IO.FS.rename \"build/other\" \"build/GaugeOwed.olean\" : IO Unit)\nnamespace Gauge\n"), 1, "changed what they are checked against"),
    ("as it is: proved", "Zeros", lambda work: None, 0, "PROVED Zeros"),
    ("the C++ loop reads one byte past the view: the proof fails", "Zeros",
     replace("model/Zeros.hpp", "i < data.size()", "i <= data.size()"), 1, "ZerosClaims.lean"),
    ("the C++ loop does not move on: the proof that it ends fails", "Zeros",
     replace("model/Zeros.hpp", "i = i + 1)", "i = i + 0)"), 1, "ZerosClaims.lean"),
    ("as it is: proved", "Bits", lambda work: None, 0, "PROVED Bits"),
    ("the C++ shifts by up to 127 of 64 bits, which is undefined: the safety proof fails", "Bits",
     replace("model/Bits.hpp", "word >> (n & 63)", "word >> (n & 127)"), 1, "BitsClaims.lean"),
    ("as it is, read from a file of another program that does not compile alone: proved", "Histogram", lambda work: None, 0, "PROVED Histogram"),
    ("a private method the public ones call indexes without its remainder: the safety proof fails", "Histogram",
     replace("sample/stats/histogram.h", "count[bin % BINS] += 1;", "count[bin] += 1;"), 1, "HistogramClaims.lean"),
    ("the C++ divides by a total it has not tested: the safety proof fails", "Histogram",
     replace("sample/stats/histogram.h", "if ( total == 0 || bin >= BINS ) {", "if ( bin >= BINS ) {"), 1, "HistogramClaims.lean"),
    ("the C++ resets the total and not the counts: the invariant's proof fails", "Histogram",
     replace("sample/stats/histogram.h", "    memset( count, 0, sizeof( count ) );\n", ""), 1, "HistogramClaims.lean"),
    ("as it is, a function that is not a method, over a pointer and a length: proved", "frame_begins", lambda work: None, 0, "PROVED frame_begins"),
    ("the function reads its fourth byte having seen that there are three: the safety proof fails", "frame_begins",
     replace("sample/wire/frame.h", "if ( n < 4 ||", "if ( n < 3 ||"), 1, "frame_beginsClaims.lean"),
    ("as it is, a method over a pointer and a length: proved", "Checksum", lambda work: None, 0, "PROVED Checksum"),
    ("the method reads the byte at its length: the proof fails", "Checksum",
     replace("sample/wire/frame.h", "i < len; i++", "i <= len; i++"), 1, "ChecksumClaims.lean"),
    ("as it is, a class and the type its methods take: both proved", "Percent Dial", lambda work: None, 0, "PROVED Dial"),
    ("the type's constructor lets 101 through: the type's own proof fails", "Percent Dial",
     replace("sample/stats/dial.h", "value( raw % 101 )", "value( raw % 102 )"), 1, "PercentClaims.lean"),
    ("the type says less than its user needs (at most 101): the type is proved, and its user's proof fails", "Percent Dial",
     replace("sample/stats/dial.h", "return value <= MOST;", "return value <= MOST + 1;"), 1, "DialClaims.lean"),
    ("the user's array is one short of what the type allows: its proof fails", "Percent Dial",
     replace("sample/stats/dial.h", "uint32_t seen[101];", "uint32_t seen[100];"), 1, "DialClaims.lean"),
    ("as it is, preconditions: a constructor's, kept by the class that makes one; a method's, kept by a method of its own class", "Score Shelf Board", lambda work: None, 0, "PROVED Board"),
    ("a caller makes a Score of any number, where at most 100 is expected: the caller's proof fails, not Score's", "Score Board",
     replace("sample/stats/grade.h", "Score s( n % 101 );", "Score s( n );"), 1, "BoardClaims.lean"),
    ("the constructor expects less than the invariant says (at most 101): Score's own proof fails", "Score",
     replace("sample/stats/grade.h", "pre( raw <= MOST )", "pre( raw <= MOST + 1 )"), 1, "ScoreClaims.lean"),
    ("a method calls another without what that one expects (first asks for place 0 of none): its proof fails", "Shelf",
     replace("sample/stats/grade.h", "    if ( used == 0 )\n      return 0;\n", ""), 1, "ShelfClaims.lean"),
    ("a method expects too little for what it does (a place up to the number used, not below it): its proof fails", "Shelf",
     replace("sample/stats/grade.h", "pre( i < used )", "pre( i <= used )"), 1, "ShelfClaims.lean"),
    ("a method says nothing of what it expects, and reads any place: its proof fails", "Shelf",
     replace("sample/stats/grade.h", "const pre( i < used ) {", "const {"), 1, "ShelfClaims.lean"),
    ("as it is, a class template, proved once of every type and bounds, and a class that takes and makes a bounded number", "bounded_of bounded_checked_of Tank", lambda work: None, 0, "PROVED Tank"),
    ("the template's constructor expects only the upper bound: the template's own proof fails", "bounded_of",
     replace("sample/strong/bounded.h", "pre( A <= raw && raw <= B )", "pre( raw <= B )"), 1, "bounded_ofClaims.lean"),
    ("a class makes a bounded number of any number: that class's proof fails, not the template's", "bounded_of bounded_checked_of Tank",
     replace("sample/strong/tank.h", "Level to( n % 101 );", "Level to( n );"), 1, "TankClaims.lean"),
    ("the bounds are wider than the class's array (0 to 101): its proof fails", "bounded_of bounded_checked_of Tank",
     replace("sample/strong/tank.h", "static const uint32_t FULL = 100;", "static const uint32_t FULL = 101;"), 1, "TankClaims.lean"),
    ("a bound the type cannot hold (-1, of an unsigned type): the compiler refuses it", "bounded_of bounded_checked_of Tank",
     replace("sample/strong/tank.h", "bounded<0, FULL, uint32_t>", "bounded<-1, FULL, uint32_t>"), 1, "cannot be narrowed"),
    ("the checked type's test lets the lower bound go: its own proof fails", "bounded_checked_of",
     replace("sample/strong/bounded.h", "STRONG_CHECK( A <= raw && raw <= B, from );", "STRONG_CHECK( raw <= B, from );"), 1, "bounded_checked_ofClaims.lean"),
    ("the checked type tests nothing: it is made of anything, and its own proof fails, so no class that takes one may rest on its bounds (from gosh, 2026-11-26)", "bounded_checked_of",
     replace("sample/strong/bounded.h", "  {\n    STRONG_CHECK( A <= raw && raw <= B, from );\n  }", "  {\n  }"), 1, "bounded_checked_ofClaims.lean"),
    ("a proved method that is not a way in tests what it is given when the program runs: refused", "bounded_of bounded_checked_of Tank",
     replace("sample/strong/tank.h", "    Level to( n % 101 );", "    STRONG_CHECK( n <= FULL, caller() );\n    Level to( n );"), 2, "which is not a `_checked` way in"),
    ("a class named before the type it uses is proved: refused", "Dial", lambda work: None, 1, "which is not proved yet"),
    ("as it is, a proof of a set: two objects of one class, and a function of the set called in it", "fits Jar",
     lambda work: None, 0, "PROVED Jar, as proofs/Jar.proof.cpp says it"),
    ("the set's function gives nothing where n is more than the room, which its own claim allows: the claim of the set is not proved", "fits Jar",
     replace("sample/set/fits.h", "  if ( n > room ) return room;", "  if ( n > room ) return 0;"), 1, "a PROVE of proofs/Jar.proof.cpp is not proved"),
    ("a function's own proof file claims more than is so (less than the room, not at most it): it is not proved", "fits",
     replace("proofs/fits.proof.cpp", "PROVE( fits( n, room ) <= room &&", "PROVE( fits( n, room ) < room &&"), 1, "a PROVE of proofs/fits.proof.cpp is not proved"),
    ("a const method handed a number says one more than there is room for: the claim of the set is not proved", "fits Jar",
     replace("sample/set/jar.h", "    if ( n > room ) return room;\n    return n;", "    if ( n > room ) return room + 1;\n    return n;"), 1, "a PROVE of proofs/Jar.proof.cpp is not proved"),
    ("the proof calls a function not proved before it: refused, not guessed", "Jar",
     lambda work: None, 1, "which is not a function of the set proved before this file"),
    ("the proof makes an object of a class not of the set: refused", "fits Jar",
     lambda work: (replace("proofs/Jar.proof.cpp", '#include "forall.h"\n', '#include "forall.h"\n\nclass Other { public: void add( uint32_t ) {} uint32_t count() const { return 0; } };\n')(work),
                   replace("proofs/Jar.proof.cpp", "    Jar b;\n", "    Other b;\n")(work)),
     1, "not one object of a class of the set"),
    ("as it is, a class that has-a two proved classes and keeps a rule that spans them: proved", "Water Tray Station",
     lambda work: None, 0, "PROVED Station"),
    ("the station tests the tank's water and not the tray's room: what the tray expects of its caller is not kept: the station is not proved", "Water Tray Station",
     replace("sample/has/station.h", "if ( water.level() < SHOT || tray.room() < DRIP ) return 0;", "if ( water.level() < SHOT ) return 0;"),
     1, "a proof does not hold (claims/StationClaims.lean)"),
    ("the tray says it has 10 ml more room than it has: the tray is still proved (it keeps its own invariant), and the station is not", "Water Tray Station",
     replace("sample/has/tray.h", "uint32_t room() const { return FULL - ml; }", "uint32_t room() const { return FULL - ml + 10; }"),
     1, "PROVED Tray"),
    ("the station counts two shots for one: the rule that spans it and the tray is broken: the station is not proved", "Water Tray Station",
     replace("sample/has/station.h", "    shots = shots + 1;", "    shots = shots + 2;"), 1, "a proof does not hold (claims/StationClaims.lean)"),
    ("the station is named before a part it has: refused, not guessed", "Water Station Tray",
     lambda work: None, 1, "it uses Tray, which is not proved yet"),
    ("a part is copied: refused (a part is changed by its own methods and nothing else)", "Water Tray Station",
     replace("sample/has/station.h", "  uint32_t pulled() const { return shots; }", "  uint32_t pulled() const { Tray t = tray; return t.held(); }"),
     2, "a local of a class's type that is not made by its constructor"),
    ("a part left out of the constructor's list (C++ would make it anyway): refused, it is made where it is written", "Water Tray Station",
     replace("sample/has/station.h", "Station() : water(), tray(), shots( 0 ) {}", "Station() : water(), shots( 0 ) {}"),
     2, "the constructor does not assign tray"),
    ("the C++ says a weaker invariant, level <= limit || true: still proved (the invariant is in the C++, for its reader)", "Gauge",
     replace("model/Gauge.hpp", "return level <= limit;", "return level <= limit || true;"), None, ""),
    ("the C++ says a stronger invariant than its methods keep: the invariant's proof fails", "Gauge",
     replace("model/Gauge.hpp", "return level <= limit;", "return level < limit;"), 1, "GaugeClaims.lean"),
    ("the generator translates wrongly: the proofs pass, and the comparison with the C++ fails", "Tally",
     model_wrong, 1, "the model and the C++ differ"),
]


def red():
    for name, klass, edit, code, expect in RED:
        got, out = prove(edit, klass)
        if code is None:
            print("%-78s (exit %d: %s)" % ("noted: " + name[:70], got, out.strip().splitlines()[-1][:60] if out.strip() else ""))
            continue
        check("%s: %s" % (klass, name), got == code and expect in out, "(exit %d) %s" % (got, out.strip()[-300:]))


def ingress_cases():
    got, out = ingress(lambda work: None)
    check("ingress: as it is, code that is not proved comes in by a checked type and method: accepted",
          got == 0 and "ingress: ok" in out, "(exit %d) %s" % (got, out.strip()[-300:]))
    got, out = ingress(replace("sample/weak/outside.h", "tank.fill_checked( LevelChecked( anything ) );",
                               "tank.fill( Level( anything ) );"))
    check("ingress: code that is not proved makes a bounded number itself, tested by nothing: refused",
          got == 1 and "outside.h:" in out and "makes a Level" in out, "(exit %d) %s" % (got, out.strip()[-300:]))
    got, out = ingress(replace("sample/weak/outside.h", "  return true;", "  return tank.at() <= 100;"))
    check("ingress: code that is not proved calls a proved method by a name that is not _checked, though nothing could fail: refused",
          got == 1 and "calls at on tank" in out, "(exit %d) %s" % (got, out.strip()[-300:]))
    def moved(work):
        shutil.move(os.path.join(work, "sample", "weak", "outside.h"), os.path.join(work, "sample", "strong", "outside.h"))
    got, out = ingress(moved)
    check("ingress: code that is not proved stands among what is: refused",
          got == 1 and "and not one of the proved classes" in out, "(exit %d) %s" % (got, out.strip()[-300:]))


LINT_STRONG = """#include <cstddef>
#include "retain.hpp"
namespace Strong {
class Reader
{
private:
  unsigned char kept[4];
  unsigned n;

public:
  Reader() : kept(), n( 0 ) {}
  bool read_checked( const unsigned char* bytes, size_t count )
  {
    n = 0;
    while ( n < 4 && n < count ) {
      kept[n] = bytes[n];
      n += 1;
    }
    return n == 4;
  }
  bool invariant() const { return n <= 4; }
};
inline bool same_checked( const unsigned char* a, size_t na, const unsigned char* b, size_t nb )
{
  return na == nb && ( na == 0 || a[0] == b[0] );
}
}
"""
LINT_RETAIN = """#pragma once
template <typename T> class retain {
  static inline thread_local retain<T>* s_current = nullptr;
  retain<T>* m_previous; T* m_as;
public:
  retain( T* as, bool use = true ) : m_previous( s_current ), m_as( as ) { if ( use ) s_current = this; }
  ~retain() { if ( s_current == this ) s_current = m_previous; }
  class iterator { retain<T>* m_at; public: iterator( retain<T>* at = nullptr ) : m_at( at ) {} T* operator->() { return m_at->m_as; } };
  static iterator begin() { return iterator( s_current ); }
  template <typename TT> friend TT*& recall();
  template <typename TT> friend bool retained();
};
template <typename T> inline bool retained() { return retain<T>::s_current != nullptr; }
template <typename T> inline T*& recall() { return retain<T>::s_current->m_as; }
"""
LINT_WINDOW = """#include <cstddef>
#include <cstdint>
namespace Strong {
template <typename Iterator> class subarray {
  Iterator first; uint64_t count;
public:
  subarray( Iterator a, uint64_t n ) : first( a ), count( n ) {}
  uint64_t size() const { return count; }
  unsigned char at( uint64_t i ) const { return *( first + i ); }
};
}
"""
LINT_WEAK = """#include "strong/reader.h"
#include "strong/subarray.h"
#include "retain.hpp"
struct Ctx { int n; };
int deep( void ) { return recall<Ctx>()->n; }
int middle( void ) { return deep(); }
int top( void ) { Ctx c = { 1 }; retain<Ctx> as( &c ); return middle(); }
typedef Strong::subarray<const unsigned char*> Eight;
bool handed( Eight window );
bool hand( void ) { unsigned char eight[8] = { 0 }; return handed( Eight( eight, 8 ) ); }
#include <signal.h>
#include <cstring>
void both( int& a, int& b ) { a += b; }
bool use( const unsigned char* data, const unsigned char* other, size_t n )
{
  Strong::Reader r;
  int x = 0, y = 0;
  both( x, y );
  signal( SIGPIPE, SIG_IGN );
  return r.read_checked( data, n ) && Strong::same_checked( data, n, other, n );
}
"""


def lint(old=None, new=None):
    """lint.py on a small program: a proved class and function under strong/, and one file that uses them."""
    weak, strong = LINT_WEAK, LINT_STRONG
    if old is not None and LINT_STRONG.count(old) == 1 and LINT_WEAK.count(old) == 0:
        strong = strong.replace(old, new)
    elif old is not None:
        assert weak.count(old) == 1, old
        weak = weak.replace(old, new)
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, "p", "strong"))
        os.makedirs(os.path.join(d, "p", "weak"))
        open(os.path.join(d, "p", "strong", "reader.h"), "w").write(strong)
        open(os.path.join(d, "p", "strong", "subarray.h"), "w").write(LINT_WINDOW)
        os.makedirs(os.path.join(d, "inc"))
        open(os.path.join(d, "inc", "retain.hpp"), "w").write(LINT_RETAIN)
        open(os.path.join(d, "p", "weak", "use.cc"), "w").write(weak)
        r = subprocess.run([sys.executable, os.path.join(HERE, "lint.py")], capture_output=True, text=True,
                           env=dict(os.environ, SUBJECT=os.path.join(d, "p"), STRONG="strong", INCLUDE=os.path.join(d, "inc")))
        return r.returncode, r.stdout + r.stderr


DOMAIN_FILES = {
    "DOMAINS": "# the two domains of a small program\nruler  ruler | ruler/ruler.h\nuser   user  | user/user.h\n",
    "ruler/ruler.h": "#pragma once\n#include \"ruler/inch.h\"\nint length( int n );\n",
    "ruler/inch.h": "#pragma once\nstruct Inch { int n; };\ninline int inches( int n ) { return n; }\n",
    "ruler/ruler.cc": "#include \"ruler/ruler.h\"\nint length( int n ) { return inches( n ) * 2; }\n",
    "user/user.h": "#pragma once\nint measured( int n );\n",
    "user/user.cc": "#include \"user/user.h\"\n#include \"ruler/ruler.h\"\nint measured( int n ) { return length( n ); }\n",
}


# The same program, ruler laid out: its ABI at the top of ruler/, its inside under ruler/imp/, in Ruler::Imp.
LAID_FILES = {
    "DOMAINS": "# the two domains of a small program, one laid out\nApp::Ruler  ruler\nuser   user  | user/user.h\n",
    "ruler/ruler.h": "#pragma once\nnamespace App::Ruler {\nint length( int n );\n}\n",
    "ruler/imp/inch.h": "#pragma once\nnamespace App::Ruler::Imp {\nstruct Inch { int n; };\ninline int inches( int n ) { return n; }\n}\n",
    "ruler/imp/ruler.cc": "#include \"ruler/ruler.h\"\n#include \"ruler/imp/inch.h\"\nint App::Ruler::length( int n ) { return App::Ruler::Imp::inches( n ) * 2; }\n",
    "user/user.h": "#pragma once\nint measured( int n );\n",
    "user/user.cc": "#include \"user/user.h\"\n#include \"ruler/ruler.h\"\nint measured( int n ) { return App::Ruler::length( n ); }\n",
}


# A program that holds a laid-out domain deeper in one named `| *` (every header its ABI), as code not yet divided may.
NESTED_FILES = {
    "DOMAINS": "App::Ruler  app/ruler\napp  app | *\n",
    "app/app.h": "#pragma once\n#include \"app/parts/part.h\"\nint measured( int n );\n",
    "app/parts/part.h": "#pragma once\ninline int part( int n ) { return n; }\n",
    "app/app.cc": "#include \"app/app.h\"\n#include \"app/ruler/ruler.h\"\nint measured( int n ) { return part( App::Ruler::length( n ) ); }\n",
    "app/ruler/ruler.h": "#pragma once\nnamespace App::Ruler {\nint length( int n );\n}\n",
    "app/ruler/imp/inch.h": "#pragma once\nnamespace App::Ruler::Imp {\ninline int inches( int n ) { return n; }\n}\n",
    "app/ruler/imp/ruler.cc": "#include \"app/ruler/ruler.h\"\n#include \"app/ruler/imp/inch.h\"\nint App::Ruler::length( int n ) { return App::Ruler::Imp::inches( n ) * 2; }\n",
}


def domain_lint(edit=None, sample=None, env=None):
    """lint.py on a small program of two domains, ruler and user, with its map; `edit(files)` changes it first."""
    files = dict(DOMAIN_FILES if sample is None else sample)
    if edit is not None:
        edit(files)
    with tempfile.TemporaryDirectory() as d:
        for rel, text in files.items():
            os.makedirs(os.path.dirname(os.path.join(d, "p", rel)), exist_ok=True)
            open(os.path.join(d, "p", rel), "w").write(text)
        os.makedirs(os.path.join(d, "p", "strong"), exist_ok=True)
        r = subprocess.run([sys.executable, os.path.join(HERE, "lint.py")], capture_output=True, text=True,
                           env=dict(os.environ, SUBJECT=os.path.join(d, "p"), STRONG="strong",
                                    **({"DOMAINS": "DOMAINS"} if "DOMAINS" in files else {}), **(env or {})))
        return r.returncode, r.stdout + r.stderr


def domain_cases():
    def case(name, edit, code, expect, sample=None, env=None):
        got, out = domain_lint(edit, sample, env)
        check("a domain: " + name, got == code and all((e[1:] not in out) if e.startswith("!") else (e in out) for e in expect),
              "(exit %d) %s" % (got, out.strip()[-400:]))

    def change(rel, old, new):
        def edit(files):
            assert files[rel].count(old) == 1, (rel, old)
            files[rel] = files[rel].replace(old, new)
        return edit

    def add(rel, text):
        def edit(files):
            files[rel] = text
        return edit
    case("as it is, one domain uses another by its ABI: accepted", None, 0, ["lint: ok", "!of ruler's inside"])
    case("a domain includes another's inside: refused",
         change("user/user.cc", '#include "ruler/ruler.h"', '#include "ruler/ruler.h"\n#include "ruler/inch.h"'), 1,
         ["user/user.cc:3: includes ruler/inch.h, of ruler's inside"])
    case("a domain uses a name of another's inside that its ABI header brings in: refused",
         change("user/user.cc", "return length( n );", "return length( inches( n ) );"), 1,
         ["user/user.cc:3: uses inches, of ruler's inside (ruler/inch.h)"])
    case("an ABI header declares a function that gives back a type of its own inside: refused",
         change("ruler/ruler.h", "int length( int n );", "int length( int n );\nInch inch( int n );"), 1,
         ["ruler/ruler.h:4: inch, of ruler's ABI, names Inch, of its inside (ruler/inch.h)"])
    case("an ABI header's inline function has a local of its inside's type: accepted (a body is not the boundary)",
         change("ruler/ruler.h", "int length( int n );", "int length( int n );\ninline int twice( int n ) { Inch i = { n }; return i.n * 2; }"), 0,
         ["lint: ok", "!names Inch"])
    case("a source of no domain: refused", add("loose/loose.cc", "int loose( void ) { return 0; }\n"), 1,
         ["loose/loose.cc: of no domain"])
    case("the map names an ABI header that is not there: refused",
         change("DOMAINS", "user/user.h\n", "user/user.h user/gone.h\n"), 1, ["user's ABI names user/gone.h, which is not there"])
    case("a crossing the map allows: said, not refused",
         lambda files: (change("user/user.cc", "return length( n );", "return length( inches( n ) );")(files),
                        change("DOMAINS", "user/user.h\n", "user/user.h\nallow user/user.cc ruler   # until ruler says inches\n")(files)), 0,
         ["lint: ok", "1 crossing into another domain's inside", "user/user.cc:3: uses inches, of ruler's inside"])
    case("a crossing the map allows that is no longer made: refused, so the line goes",
         change("DOMAINS", "user/user.h\n", "user/user.h\nallow user/user.cc ruler\n"), 1,
         ["allows user/user.cc to reach ruler's inside, and it no longer does"])
    case("laid out, used by its ABI, its inside in App::Ruler::Imp: accepted", None, 0, ["lint: ok", "!App::Ruler's inside"], LAID_FILES)
    case("laid out: another domain uses a name of App::Ruler::Imp: refused",
         lambda files: (change("user/user.cc", '#include "ruler/ruler.h"', '#include "ruler/ruler.h"\n#include "ruler/imp/inch.h"')(files),
                        change("user/user.cc", "return App::Ruler::length( n );", "return App::Ruler::length( App::Ruler::Imp::inches( n ) );")(files)), 1,
         ["user/user.cc:3: includes ruler/imp/inch.h, of App::Ruler's inside", "user/user.cc:4: uses inches, of App::Ruler's inside"], LAID_FILES)
    case("laid out: a header under imp/ declares outside App::Ruler::Imp: refused",
         change("ruler/imp/inch.h", "\n}\n", "\n}\ninline int feet( int n ) { return n * 12; }\n"), 1,
         ["ruler/imp/inch.h:6: feet is of App::Ruler's inside (imp/), and is declared outside App::Ruler::Imp"], LAID_FILES)
    case("laid out: an ABI header declares into App::Ruler::Imp: refused",
         change("ruler/ruler.h", "int length( int n );", "int length( int n );\nnamespace Imp { struct Yard { int n; }; }"), 1,
         ["ruler/ruler.h:4: Yard is declared into App::Ruler::Imp by an ABI header"], LAID_FILES)
    case("laid out: an ABI header declares outside App::Ruler: refused",
         change("ruler/ruler.h", "\n}\n", "\n}\nint loose( int n );\n"), 1,
         ["ruler/ruler.h:5: loose is of App::Ruler's ABI, and is declared outside App::Ruler"], LAID_FILES)
    case("laid out: another domain declares into App::Ruler::Imp: refused",
         change("user/user.h", "int measured( int n );", "int measured( int n );\nnamespace App::Ruler::Imp { int borrowed( int n ); }"), 1,
         ["user/user.h:3: borrowed is declared into App::Ruler::Imp by a file of user"], LAID_FILES)
    case("laid out: an ABI header declares main, and a function of C's linkage, in no namespace: accepted (the language puts them there)",
         change("ruler/ruler.h", "\n}\n", "\n}\nextern \"C\" int ruler_hook( int n );\nint main( void );\n"), 0,
         ["lint: ok", "!declared outside"], LAID_FILES)
    case("laid out: an ABI header declares outside App::Ruler, and the map allows it: said, not refused",
         lambda files: (change("ruler/ruler.h", "\n}\n", "\n}\nint loose( int n );\n")(files),
                        change("DOMAINS", "App::Ruler  ruler\n", "App::Ruler  ruler\nallow ruler/ruler.h App::Ruler   # as another program declares it\n")(files)), 0,
         ["lint: ok", "1 crossing", "ruler/ruler.h:5: loose is of App::Ruler's ABI, and is declared outside App::Ruler"], LAID_FILES)
    case("laid out: another domain declares into App::Ruler, and the map allows it by naming App::Ruler: said, not refused",
         lambda files: (change("user/user.h", "int measured( int n );", "int measured( int n );\nnamespace App::Ruler { int borrowed( int n ); }")(files),
                        change("DOMAINS", "App::Ruler  ruler\n", "App::Ruler  ruler\nallow user/user.h App::Ruler   # by an older naming\n")(files)), 0,
         ["lint: ok", "1 crossing", "user/user.h:3: borrowed is declared into App::Ruler by a file of user"], LAID_FILES)
    case("a header says `using namespace` outside a function: refused",
         change("user/user.h", "int measured( int n );", "int measured( int n );\nnamespace App::Ruler {}\nusing namespace App::Ruler;"), 1,
         ["user/user.h:4: a header says `using namespace` outside a function"], LAID_FILES)
    case("`| *`: every header of the domain is of its ABI, at any depth: another's use of it accepted",
         lambda files: (change("DOMAINS", "ruler  ruler | ruler/ruler.h\n", "ruler  ruler | *\n")(files),
                        change("user/user.cc", '#include "ruler/ruler.h"', '#include "ruler/ruler.h"\n#include "ruler/inch.h"')(files),
                        change("user/user.cc", "return length( n );", "return length( inches( n ) );")(files)), 0,
         ["lint: ok", "!of ruler's inside"])
    case("`| *` around a domain laid out deeper: its headers at any depth are its ABI, and the deeper one's are not",
         None, 0, ["lint: ok", "!inside"], NESTED_FILES)
    case("`| *` around a domain laid out deeper: a use of the deeper one's inside is refused",
         lambda files: (change("app/app.cc", '#include "app/ruler/ruler.h"', '#include "app/ruler/ruler.h"\n#include "app/ruler/imp/inch.h"')(files),
                        change("app/app.cc", "App::Ruler::length( n )", "App::Ruler::Imp::inches( n )")(files)), 1,
         ["app/app.cc:3: includes app/ruler/imp/inch.h, of App::Ruler's inside", "app/app.cc:4: uses inches, of App::Ruler's inside"], NESTED_FILES)
    case("`| *`: its own header's `using namespace`, and its ABI naming its inside, are not refused (its boundary is not drawn)",
         lambda files: (change("app/parts/part.h", "inline int part", "namespace Bits { struct Bit { int n; }; }\nusing namespace Bits;\ninline int part")(files),
                        add("app/parts/bit.cc", "struct Hidden { int n; };\n")(files),
                        change("app/app.h", "int measured( int n );", "int measured( int n );\nstruct Hidden;\nHidden* hidden( void );")(files)), 0,
         ["lint: ok", "!using namespace", "!names Hidden"], NESTED_FILES)
    case("a domain laid out: the same `using namespace` in its header is refused",
         change("app/ruler/ruler.h", "int length( int n );", "int length( int n );\nnamespace Bits {}\nusing namespace Bits;"), 1,
         ["a header says `using namespace` outside a function"], NESTED_FILES)
    case("RULES=\"a domain\": that rule alone: a thread started beside state all share is not refused",
         add("user/threads.cc", "#include <thread>\nint shared = 0;\nvoid go( void ) { std::thread t( [] { shared++; } ); t.join(); }\n"), 0,
         ["lint: ok", "by the rule a domain alone", "!a thread is started"], None, {"RULES": "a domain"})
    case("without RULES, the same thread is refused (the case above is not the program's doing)",
         add("user/threads.cc", "#include <thread>\nint shared = 0;\nvoid go( void ) { std::thread t( [] { shared++; } ); t.join(); }\n"), 1,
         ["a thread is started"])
    case("RULES=\"a domain\": a domain that includes another's inside is still refused",
         change("user/user.cc", '#include "ruler/ruler.h"', '#include "ruler/ruler.h"\n#include "ruler/inch.h"'), 1,
         ["user/user.cc:3: includes ruler/inch.h, of ruler's inside"], None, {"RULES": "a domain"})
    case("a source that reads only as the build has it, without FLAGS: refused, as not read whole",
         add("user/built.cc", "#ifndef BUILT\n#error not as built\n#endif\nint built( void ) { return 1; }\n"), 1,
         ["user/built.cc: not as built"])
    case("and with FLAGS that say it (-DBUILT): read, and accepted",
         add("user/built.cc", "#ifndef BUILT\n#error not as built\n#endif\nint built( void ) { return 1; }\n"), 0,
         ["lint: ok"], None, {"FLAGS": "-DBUILT"})
    case("RULES of another rule: it will not start",
         None, 1, ["RULES may say only"], None, {"RULES": "one name"})
    case("without a map, the rule is off: accepted, the inside used and all",
         lambda files: (files.pop("DOMAINS"), change("user/user.cc", "return length( n );", "return length( inches( n ) );")(files)), 0,
         ["lint: ok"])


def lint_cases():
    def case(name, old, new, code, expect):
        got, out = lint(old, new)
        check("lint: " + name, got == code and all((e[1:] not in out) if e.startswith("!") else (e in out) for e in expect), "(exit %d) %s" % (got, out.strip()[-400:]))
    case("as it is, what is proved is called with arguments that are apart: accepted", None, None, 0,
         ["lint: ok: 3 files", "4 of them of what is under strong/"])
    case("a proved method is handed its own object as the bytes to read: refused",
         "r.read_checked( data, n )", "r.read_checked( reinterpret_cast<const unsigned char*>( &r ), n )", 1,
         ["the object and `bytes` of read_checked are one thing", "the address of a Reader is taken"])
    case("a proved function is handed one thing as two arguments it only reads: accepted (non-const aliases are unique; const ones may not be)",
         "same_checked( data, n, other, n )", "same_checked( data, n, data, n )", 0,
         ["lint: ok", "!are one thing"])
    case("a proved function is handed a part of what its other argument is, both only read: accepted",
         "same_checked( data, n, other, n )", "same_checked( data, n, &data[2], n )", 0,
         ["lint: ok", "!are one thing"])
    case("an argument of what is proved that is not a name, and nothing written: accepted",
         "same_checked( data, n, other, n )", "same_checked( data, n, n ? other : data, n )", 0,
         ["lint: ok", "!not a name"])
    case("an argument of what is proved that is not a name, beside the object it writes: refused (hand a name)",
         "r.read_checked( data, n )", "r.read_checked( n ? other : data, n )", 1,
         ["the object and `bytes` (`n ? other : data`, not a name) of read_checked may be one thing, and one may be written"])
    case("one thing as two arguments of what is not proved, one written: refused too",
         "both( x, y );", "both( x, x );", 1, ["weak/use.cc:", "`a` and `b` of both are one thing", "and one may be written"])
    case("one thing as two arguments of what is not proved, both only read: accepted",
         "void both( int& a, int& b ) { a += b; }",
         "void both( int& a, int& b ) { a += b; }\nint peek( const int& a, const int& b ) { return a + b; }\nint peeked( void ) { int z = 1; return peek( z, z ); }", 0,
         ["lint: ok", "!are one thing"])
    case("one thing as two arguments of what is the system's: said, not refused",
         "both( x, y );", "both( x, y ); sigprocmask( 0, (sigset_t*)data, (sigset_t*)data ); (void)memcmp( data, data, n );", 0,
         ["1 pair of arguments that are one thing, in calls of what is not this program's"])
    case("a thread is started, and nothing that can be written is shared: said", "#include <signal.h>", "#include <signal.h>\n#include <thread>\nvoid work( void ) {}",
         0, ["lint: ok"])
    started = ("int x = 0, y = 0;", "int x = 0, y = 0; std::thread worker( work ); worker.join();")
    def two(name, old2, new2, code, expect):
        global LINT_WEAK
        kept = LINT_WEAK
        LINT_WEAK = LINT_WEAK.replace("#include <signal.h>", "#include <signal.h>\n#include <thread>\nvoid work( void ) {}").replace(*started)
        try:
            case(name, old2, new2, code, expect)
        finally:
            LINT_WEAK = kept
    two("a thread is started with nothing shared: said, each start", None, None, 0, ["1 thread started", "weak/use.cc:"])
    two("a thread is started beside a global that can be written: refused", "void both(", "int counted = 0;\nvoid both(", 1,
        ["a thread is started, and there is state that can be written", "`counted` can be written"][:1])
    case("a global that can be written, and no thread: said", "void both(", "int counted = 0;\nvoid both(", 0,
         ["1 thing that can be written and shared by every object and thread", "`counted`"])
    case("a static in a function that can be written: said", "int x = 0, y = 0;", "int x = 0, y = 0; static int calls = 0; calls += 1;", 0,
         ["`calls` can be written"])
    case("a static member that can be written: said", "void both(", "struct Counts { static int made; };\nint Counts::made = 0;\nvoid both(", 0,
         ["`made` can be written"])
    case("a global that cannot be written, one that is each thread's own, and one made for many threads: none is shared state",
         "void both(", "#include <atomic>\nconst int fixed = 3;\nstatic const char* const name = \"n\";\nconst char words[] = \"w\";\nstatic const int table[2] = { 1, 2 };\nthread_local int mine = 0;\nstd::atomic<int> all( 0 );\nvoid both(", 0, ["lint: ok", "!can be written"])
    case("a static that can be written under strong/: refused", "inline bool same_checked(", "static int seen_before = 0;\ninline bool same_checked(", 1,
         ["reader.h:", "`seen_before` can be written"])
    case("a thread named in a comment is not one", "int x = 0, y = 0;", "int x = 0, y = 0; /* no std::thread here */", 0, ["lint: ok"])
    case("a signal handler that is a function is said", "signal( SIGPIPE, SIG_IGN );", "signal( SIGPIPE, SIG_IGN ); signal( SIGINT, (void (*)(int))0 ); sigaction( SIGINT, 0, 0 );", 0,
         ["1 signal handler", "weak/use.cc:"])
    case("the address of a proved value is taken outside: refused",
         "int x = 0, y = 0;", "int x = 0, y = 0; Strong::Reader* p = &r; (void)p;", 1, ["the address of a Reader is taken"])
    case("a reference to a proved value is cast to something else outside: refused",
         "int x = 0, y = 0;", "int x = 0, y = 0; unsigned& u = reinterpret_cast<unsigned&>( r ); (void)u;", 1,
         ["a Reader is cast to something else"])
    case("a proved value is a member of a union outside: refused",
         "void both(", "union Either { Strong::Reader r; int i; Either() : i( 0 ) {} };\nvoid both(", 1,
         ["a Reader is a member of a union"])
    make = "bool hand( void ) { unsigned char eight[8] = { 0 }; return handed( Eight( eight, 8 ) ); }"
    case("a window's byte is read outside: refused", make,
         "bool hand( void ) { unsigned char eight[8] = { 0 }; Eight w( eight, 8 ); return w.at( 0 ) == 0; }", 1, ["at is called"])
    case("a window is kept in a field: refused", make, make + "\nstruct Keeps { Eight kept; };", 1,
         ["a subarray, a window on an array, is a field"])
    case("a window is a static: refused", make,
         "bool hand( void ) { static unsigned char eight[8]; static Eight kept( eight, 8 ); return handed( kept ); }", 1,
         ["is a global or a static"])
    case("a window is what a function gives back: refused", make,
         make + "\nEight give( void ) { unsigned char gone[8] = { 0 }; return Eight( gone, 8 ); }", 1,
         ["is what a function gives back"])
    case("a window made outside is said, each place", None, None, 0, ["1 window made by code that is not proved", "weak/use.cc:"])
    named = "bool hand( void ) { unsigned char eight[8] = { 0 }; Eight w( eight, 8 ); %s return handed( w ); }"
    case("a window with a name, and nothing changes what it was made from: accepted", make, named % "", 0, ["lint: ok"])
    case("what a window was made from is assigned to while it is in scope: refused", make, named % "eight[0] = 1;", 1,
         ["a window was made of this at line", "and here it is assigned to"])
    case("what a window was made from is handed to what may write it: refused", make,
         "void fill( unsigned char* into );\n" + named % "fill( eight );", 1, ["it is handed to fill, which may write it"])
    case("what a window was made from has a method that is not const called on it: refused", make,
         "#include <string>\n"
         "bool hand( void ) { std::string g( 8, 'x' ); Eight w( reinterpret_cast<const unsigned char*>( g.data() ), 8 ); g.clear(); return handed( w ); }", 1,
         ["clear, which is not const, is called on it"])
    keeps = "\nclass Keeps { int kept[4]; int one;\npublic:\n  %s\n};"
    case("a method of a class that is not proved gives back a reference to its own state: said", make,
         make + keeps % "const int& first( void ) const { return kept[0]; }", 0,
         ["1 method of a class that is not proved that give back what is of their own object", "first gives back what is of its own object (kept.[0])"])
    case("a method gives back a pointer to its own state: said", make, make + keeps % "int* where( void ) { return &one; }", 0,
         ["where gives back what is of its own object (one)"])
    case("a method gives back its own state by a local, with a number added: said", make,
         make + keeps % "const int* later( void ) const { const int* p = 0; p = kept; return p + 1; }", 0,
         ["later gives back what is of its own object (kept)"])
    case("a method that is not public gives back its own state: it does not leave by that", make,
         make + keeps.replace("public:", "private:") % "int* where( void ) { return &one; }", 0, ["lint: ok"])
    case("a method that gives back its own object is not one that lets state leave", make,
         make + keeps % "Keeps& again( void ) { one += 1; return *this; }", 0, ["lint: ok"])
    case("a method of a class under strong/ gives back a pointer to its own state: refused",
         "  bool invariant() const { return n <= 4; }", "  bool invariant() const { return n <= 4; }\n  const unsigned char* bytes( void ) const { return kept; }", 1,
         ["reader.h:", "bytes gives back what is of its own object (kept)"])
    top = "int top( void ) { Ctx c = { 1 }; retain<Ctx> as( &c ); return middle(); }"
    case("a context is retained above everything that recalls it: nothing is said", None, None, 0, ["lint: ok", "!needs a"])
    case("nothing retains what is recalled, in a function nothing here calls: said, as entered from outside", top,
         "int top( void ) { return middle(); }", 0, ["1 function nothing of this program calls that need a context retained", "top needs a Ctx retained"])
    case("main needs a context and retains none: refused", top, "int main( void ) { return middle(); }", 1, ["main needs a Ctx retained"])
    case("main retains it first: accepted", top, "int main( void ) { Ctx c = { 1 }; retain<Ctx> as( &c ); return middle(); }", 0, ["lint: ok", "!needs a"])
    case("a call that needs the context comes before it is retained: the need goes on up", top,
         "int main( void ) { int early = middle(); Ctx c = { 1 }; retain<Ctx> as( &c ); return middle() + early; }", 1, ["main needs a Ctx retained"])
    case("what was recalled is kept in a field: refused", top, top + "\nstruct Holds { Ctx* held; void take( void ) { held = recall<Ctx>(); } };", 1,
         ["what was recalled is kept in a field or a global"])
    case("what a function gives back from a recall is kept in a static: refused", top,
         top + "\nCtx* now( void ) { return recall<Ctx>(); }\nvoid take( void ) { static Ctx* held = now(); (void)held; }", 1, ["what was recalled is kept in `held`"])
    case("a value read from what was recalled is not the context kept", top, top + "\nstruct Copies { int n; void take( void ) { n = recall<Ctx>()->n; } };", 0, ["lint: ok"])
    case("what is recalled is pointed elsewhere: refused", "int deep( void ) { return recall<Ctx>()->n; }",
         "int deep( void ) { static Ctx other = { 2 }; recall<Ctx>() = &other; return 0; }", 1, ["what is recalled is pointed elsewhere"])
    case("the frames above are walked: refused", "int deep( void ) { return recall<Ctx>()->n; }",
         "int deep( void ) { return retain<Ctx>::begin()->n + recall<Ctx>()->n; }", 1, ["the frames above are walked"])
    case("a retain that is a static: refused", top, "int top( void ) { static Ctx c = { 1 }; static retain<Ctx> as( &c ); return middle(); }", 1,
         ["a retain of Ctx that is not a local"])
    case("a retain that is a field: refused", top, top + "\nstruct Has { retain<Ctx> kept; };", 1, ["a retain of Ctx that is not a local"])
    case("what is retained is also handed to what recalls it: refused", top,
         "int with( Ctx& c ) { return c.n + deep(); }\nint top( void ) { Ctx c = { 1 }; retain<Ctx> as( &c ); return with( c ); }", 1,
         ["what is retained as the Ctx is also handed to with"])
    case("what is proved recalls a context: refused", "inline bool same_checked(",
         "struct Ctx;\ninline bool asks( void ) { return retained<Ctx>(); }\ninline bool same_checked(", 1, ["reader.h:", "Ctx is asked for by retained"])
    case("a file that cannot be read whole: refused, and nothing said of it",
         '#include <signal.h>', '#include <signal.h>\n#include "nowhere.h"', 1, ["could not be read whole", "weak/use.cc"])


def fixed_windows():
    """A Strong::fixed<N, of> is a window of N bytes by its type (the PRELUDE says it, as gosh's
    subarray.h does): read at an index written out below N, so the model reads it with no failure,
    and its size() is N. Any other index is refused, not modelled."""
    reader = """#pragma once
#include <cstdint>
class A {
public:
  A() : n( 0 ) {}
  void f( Strong::fixed<4> d ) { n = d.at( 0 ); n = n + d.at( %s ); n = n + d.size(); }
  bool invariant() const { return true; }
private:
  uint64_t n;
};
"""
    for name, index, code, expect in [("an index below its length: read with no failure, and its size is its length", "3", 0, None),
                                      ("an index at its length: refused", "4", 2, "not written out below 4"),
                                      ("an index that is not written out: refused", "n", 2, "not written out below 4")]:
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "A.hpp")
            open(path, "w").write(reader % index)
            r = subprocess.run([sys.executable, os.path.join(HERE, "prooc.py"), path, "--class", "A", "-o", os.path.join(d, "gen")],
                               capture_output=True, text=True)
            if code:
                check("fixed window: " + name, r.returncode == code and expect in r.stderr, "(exit %d) %s" % (r.returncode, r.stderr.strip()[-200:]))
            else:
                model = open(os.path.join(d, "gen", "AModel.lean")).read() if r.returncode == 0 else ""
                check("fixed window: " + name, "(Prooc.Bytes.byte d 3)" in model and "4#64" in model and "Prooc.Bytes.read" not in model,
                      "(exit %d) %s" % (r.returncode, r.stderr.strip()[-200:]))


def looping_asks():
    """A PROVE may name what a const method that loops gives (course/mergesort's outOfOrder): its
    model takes fuel, as every method that loops does, and the statement says some fuel is enough,
    each call its own. Without it the statement does not type-check, and Lean refuses it (found
    2026-11-21, by the course's merge sort)."""
    klass = """#pragma once
#include <cstdint>
class C {
public:
  C() : n( 0 ) {}
  void set( uint64_t v ) { n = v; if ( n > 9 ) { n = 9; } }
  uint64_t steps() const { uint64_t k = 0; for ( uint64_t i = 0; i < n; i = i + 1 ) { k = k + 1; } return k; }
  bool invariant() const { return n <= 9; }
private:
  uint64_t n;
};
"""
    proof = """#include <cstdint>
#include "C.hpp"
#include "forall.h"
PROOF( steps_are_at_most_nine )
{
  C c;
  for ( uint64_t v : all<uint64_t>() ) {
    c.set( v );
    PROVE( c.steps() <= 9 && c.steps() <= 9 );
  }
}
"""
    with tempfile.TemporaryDirectory() as d:
        open(os.path.join(d, "C.hpp"), "w").write(klass)
        open(os.path.join(d, "C.proof.cpp"), "w").write(proof)
        gen, build = os.path.join(d, "gen"), os.path.join(d, "build")
        os.makedirs(build)
        steps = [[sys.executable, os.path.join(HERE, "prooc.py"), os.path.join(d, "C.hpp"), "--class", "C", "-o", gen],
                 [sys.executable, os.path.join(HERE, "proofs.py"), os.path.join(d, "C.proof.cpp"), "--class", "C", "--named", "C",
                  "-I" + d, "-I" + os.path.join(HERE, "model"), "-o", gen]]
        shutil.copy(os.path.join(HERE, "Prooc.lean"), build)
        for m in ["Prooc", "CModel", "CProofOwed"]:      # (lean reads only what is under the directory it runs in)
            src = os.path.join("build", "Prooc.lean") if m == "Prooc" else os.path.join("gen", m + ".lean")
            steps.append([LEAN, "-o", os.path.join("build", m + ".olean"), src])
        out = ""
        for step in steps:
            r = subprocess.run(step, capture_output=True, text=True, cwd=d, env=dict(os.environ, LEAN_PATH="build"))
            out = r.stdout + r.stderr
            if r.returncode != 0:
                break
        said = open(os.path.join(gen, "CProofOwed.lean")).read() if os.path.exists(os.path.join(gen, "CProofOwed.lean")) else ""
        check("a const method that loops, in a PROVE: some fuel is enough, each call its own, and Lean takes the statement",
              r.returncode == 0 and "C.steps fuel" in said and re.search(r"∃ (fuel\d+) r\d+ (?!\1)(fuel\d+) r\d+,", said) is not None,
              "(exit %d) %s" % (r.returncode, out.strip()[-300:]))


if len(sys.argv) > 1:      # only the red cases whose names have one of these words
    RED = [c for c in RED if any(w in c[0] for w in sys.argv[1:])]
else:
    refusals()
    fixed_windows()
    looping_asks()
    ingress_cases()
    lint_cases()
    domain_cases()
red()
print("FAIL: %d" % len(failures) if failures else "PASS")
sys.exit(1 if failures else 0)
