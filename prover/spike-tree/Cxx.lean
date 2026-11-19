/-! A SPIKE (2026-11-18): what the C++ of the subset means, said once, in Lean.

Today `prooc.py` writes each method's meaning as Lean text, and that is trusted. Here the meaning
is `Cxx.exec`, below, over a tree of the method's own words; the generator's part is to copy the
tree out of the compiler's reading, and that copy is checked: `Cxx.Stmt.tokens` writes the tree
back as words, and the kernel is asked that they are the method's (`..._text`). Then the kernel is
asked, for each method, that `exec` of the tree is the model the generator wrote (`..._agrees`):
so the model, and every proof about it, is about what this file says the words mean.

Only what Gauge and Climb need is here: unsigned numbers, `int` literals, names, + - * & | ^,
comparisons, assignment, a local with a first value, `if`, `for`, `while`, `return`. A loop runs
for at most `fuel` rounds, as the model's does: no result if that is not enough. No `break` or
`continue`, no arrays, calls or views. -/

namespace Cxx

inductive Ty where
  | u8 | u16 | u32 | u64 | int
  deriving DecidableEq, Repr

/-- A number, with its type. `int` is the type of a literal: 32 bits, signed. -/
inductive Val where
  | u8 (v : BitVec 8) | u16 (v : BitVec 16) | u32 (v : BitVec 32) | u64 (v : BitVec 64) | int (v : BitVec 32)

/-- Names and what they hold. `none`: declared, and not yet given a value (to read it is undefined). -/
abbrev Store := List (String × Option Val)

def Store.get : Store → String → Option Val
  | [], _ => none
  | (k, v) :: rest, n => if k = n then v else Store.get rest n

def Store.has : Store → String → Bool
  | [], _ => false
  | (k, _) :: rest, n => k = n || Store.has rest n

def Store.set : Store → String → Val → Store
  | [], _, _ => []
  | (k, v) :: rest, n, x => if k = n then (k, some x) :: rest else (k, v) :: Store.set rest n x

inductive BinOp where
  | add | sub | mul | and | or | xor

inductive CmpOp where
  | lt | le | gt | ge | eq | ne

inductive Expr where
  | lit (n : Nat)                       -- an integer literal: an `int`
  | name (x : String)                   -- a local or a parameter if there is one of that name; else a field
  | conv (to : Ty) (e : Expr)           -- a conversion C++ makes without being asked: no words of its own
  | bin (op : BinOp) (a b : Expr)
  | cmp (op : CmpOp) (a b : Expr)
  | paren (e : Expr)
  | truth (b : Bool)                    -- `true`, `false`

inductive Stmt where
  | skip
  | seq (a b : Stmt)
  | block (s : Stmt)
  | set (x : String) (e : Expr)         -- `x = e;`
  | decl (type : String) (x : String) (e : Expr)                        -- `uint32_t x = e;`
  | forLoop (init : Stmt) (c : Expr) (x : String) (e : Expr) (body : Stmt)   -- `for (init c; x = e) body`
  | whileLoop (c : Expr) (body : Stmt)
  | ite (c : Expr) (t : Stmt) (hasElse : Bool) (e : Stmt)
  | ret (e : Option Expr)

/-- The state a method runs in: the object's fields, and its parameters and locals. -/
structure St where
  fields : Store
  locals : Store

def BinOp.on (op : BinOp) (a b : BitVec w) : BitVec w :=
  match op with
  | .add => a + b | .sub => a - b | .mul => a * b | .and => a &&& b | .or => a ||| b | .xor => a ^^^ b

def CmpOp.on (op : CmpOp) (a b : BitVec w) : Bool :=
  match op with
  | .lt => decide (a < b) | .le => decide (a ≤ b) | .gt => decide (a > b) | .ge => decide (a ≥ b)
  | .eq => decide (a = b) | .ne => decide (a ≠ b)

/-- Two numbers of one unsigned type. Anything else is not in the subset: no result. -/
def Val.bin (op : BinOp) : Val → Val → Option Val
  | .u8 a, .u8 b => some (.u8 (op.on a b)) | .u16 a, .u16 b => some (.u16 (op.on a b))
  | .u32 a, .u32 b => some (.u32 (op.on a b)) | .u64 a, .u64 b => some (.u64 (op.on a b))
  | _, _ => none

def Val.cmp (op : CmpOp) : Val → Val → Option Bool
  | .u8 a, .u8 b => some (op.on a b) | .u16 a, .u16 b => some (op.on a b)
  | .u32 a, .u32 b => some (op.on a b) | .u64 a, .u64 b => some (op.on a b)
  | _, _ => none

/-- A conversion to an unsigned type: the low bits, an `int` first extended with its sign. -/
def Val.conv (to : Ty) (v : Val) : Option Val :=
  let wide : BitVec 64 := match v with
    | .u8 a => a.setWidth 64 | .u16 a => a.setWidth 64 | .u32 a => a.setWidth 64 | .u64 a => a
    | .int a => a.signExtend 64
  match to with
  | .u8 => some (.u8 (wide.setWidth 8)) | .u16 => some (.u16 (wide.setWidth 16))
  | .u32 => some (.u32 (wide.setWidth 32)) | .u64 => some (.u64 wide)
  | .int => none

def eval : Expr → St → Option Val
  | .lit n, _ => if n < 2147483648 then some (.int (BitVec.ofNat 32 n)) else none
  | .name x, s => if s.locals.has x then s.locals.get x else s.fields.get x
  | .conv to e, s => (eval e s).bind (Val.conv to)
  | .bin op a b, s => (eval a s).bind fun x => (eval b s).bind fun y => Val.bin op x y
  | .paren e, s => eval e s
  | .cmp _ _ _, _ => none
  | .truth _, _ => none

def cond : Expr → St → Option Bool
  | .cmp op a b, s => (eval a s).bind fun x => (eval b s).bind fun y => Val.cmp op x y
  | .paren e, s => cond e s
  | .truth b, _ => some b
  | _, _ => none

/-- How a statement ends: it goes on, or the method has returned (with the fields as they then are). -/
inductive Flow where
  | go (s : St)
  | back (fields : Store) (v : Option Val)

/-- The type a word names. -/
def Ty.ofWord : String → Option Ty
  | "uint8_t" => some .u8 | "uint16_t" => some .u16 | "uint32_t" => some .u32 | "uint64_t" => some .u64
  | _ => none

/-- What comes after a statement, if it went on. -/
def andThen (r : Option Flow) (next : St → Option Flow) : Option Flow :=
  match r with
  | some (.go s) => next s
  | r => r

/-- `x = e`: a local or a parameter of that name if there is one; else a field. -/
def assign (x : String) (e : Expr) (s : St) : Option Flow :=
  (eval e s).bind fun v =>
    if s.locals.has x then some (.go { s with locals := s.locals.set x v })
    else if s.fields.has x then some (.go { s with fields := s.fields.set x v })
    else none

/-- The end of a block: the locals declared in it are gone. -/
def leave (n : Nat) (r : Option Flow) : Option Flow :=
  match r with
  | some (.go s) => some (.go { s with locals := s.locals.take n })
  | r => r

/-- A loop: while the condition is so, a round; `none` if `left` rounds are not enough. -/
def iterate (c : St → Option Bool) (round : St → Option Flow) : Nat → St → Option Flow
  | 0, _ => none
  | left + 1, s => (c s).bind fun b => if b then andThen (round s) (iterate c round left) else some (.go s)

def exec (fuel : Nat) : Stmt → St → Option Flow
  | .skip, s => some (.go s)
  | .seq a b, s => andThen (exec fuel a s) (exec fuel b)
  | .block a, s => leave s.locals.length (exec fuel a s)
  | .set x e, s => assign x e s
  | .decl type x e, s => (Ty.ofWord type).bind fun t => (eval e s).bind fun v => (Val.conv t v).bind fun v =>
      if s.locals.has x then none else some (.go { s with locals := s.locals ++ [(x, some v)] })
  | .forLoop init c x e body, s =>
      leave s.locals.length (andThen (exec fuel init s)
        (iterate (cond c) (fun s => andThen (exec fuel body s) (assign x e)) fuel))
  | .whileLoop c body, s => iterate (cond c) (exec fuel body) fuel s
  | .ite c t _ e, s => (cond c s).bind fun b => if b then exec fuel t s else exec fuel e s
  | .ret none, s => some (.back s.fields none)
  | .ret (some e), s => (eval e s).bind fun v => some (.back s.fields (some v))

structure Method where
  void : Bool
  body : Stmt

/-- A call: the fields after it, and what it gave back. To fall off the end of a method that is
to give something back is undefined. -/
def finish (void : Bool) (r : Option Flow) : Option (Store × Option Val) :=
  match r with
  | some (.back fields v) => some (fields, v)
  | some (.go s) => if void then some (s.fields, none) else none
  | none => none

def call (m : Method) (fuel : Nat) (fields args : Store) : Option (Store × Option Val) :=
  finish m.void (exec fuel m.body ⟨fields, args⟩)

/-! For the kernel to be shown that a tree's meaning is a model: a branch is taken through what
comes after it, on both sides, until the two are the same text. -/

/-! What `exec` is of each kind of statement but a loop. A loop's is said for each loop apart, by
the file made for its class: so that a loop is taken whole, and its rounds are not opened. -/
theorem exec_skip (fuel : Nat) (s : St) : exec fuel .skip s = some (.go s) := rfl
theorem exec_seq (fuel : Nat) (a b : Stmt) (s : St) : exec fuel (.seq a b) s = andThen (exec fuel a s) (exec fuel b) := rfl
theorem exec_block (fuel : Nat) (a : Stmt) (s : St) : exec fuel (.block a) s = leave s.locals.length (exec fuel a s) := rfl
theorem exec_set (fuel : Nat) (x : String) (e : Expr) (s : St) : exec fuel (.set x e) s = assign x e s := rfl
theorem exec_decl (fuel : Nat) (t x : String) (e : Expr) (s : St) : exec fuel (.decl t x e) s =
    (Ty.ofWord t).bind fun t => (eval e s).bind fun v => (Val.conv t v).bind fun v =>
      if s.locals.has x then none else some (.go { s with locals := s.locals ++ [(x, some v)] }) := rfl
theorem exec_ite (fuel : Nat) (c : Expr) (t e : Stmt) (h : Bool) (s : St) : exec fuel (.ite c t h e) s =
    (cond c s).bind fun b => if b then exec fuel t s else exec fuel e s := rfl
theorem exec_ret_none (fuel : Nat) (s : St) : exec fuel (.ret none) s = some (.back s.fields none) := rfl
theorem exec_ret_some (fuel : Nat) (e : Expr) (s : St) : exec fuel (.ret (some e)) s =
    (eval e s).bind fun v => some (.back s.fields (some v)) := rfl

theorem andThen_go (s : St) (k : St → Option Flow) : andThen (some (.go s)) k = k s := rfl
theorem andThen_back (s : Store) (v : Option Val) (k : St → Option Flow) : andThen (some (.back s v)) k = some (.back s v) := rfl
theorem andThen_none (k : St → Option Flow) : andThen none k = none := rfl
theorem finish_back (b : Bool) (s : Store) (v : Option Val) : finish b (some (.back s v)) = some (s, v) := rfl
theorem leave_go (n : Nat) (s : St) : leave n (some (.go s)) = some (.go { s with locals := s.locals.take n }) := rfl
theorem leave_back (n : Nat) (s : Store) (v : Option Val) : leave n (some (.back s v)) = some (.back s v) := rfl
theorem leave_none (n : Nat) : leave n none = none := rfl
theorem leave_ite [Decidable c] (n : Nat) (a b : Option Flow) :
    leave n (if c then a else b) = if c then leave n a else leave n b := by split <;> rfl
theorem iterate_zero (c : St → Option Bool) (r : St → Option Flow) (s : St) : iterate c r 0 s = none := rfl
theorem iterate_succ (c : St → Option Bool) (r : St → Option Flow) (left : Nat) (s : St) :
    iterate c r (left + 1) s = (c s).bind fun b => if b then andThen (r s) (iterate c r left) else some (.go s) := rfl
theorem finish_go (b : Bool) (s : St) : finish b (some (.go s)) = if b then some (s.fields, none) else none := rfl
theorem finish_none (b : Bool) : finish b none = none := rfl

theorem andThen_ite [Decidable c] (a b : Option Flow) (k : St → Option Flow) :
    andThen (if c then a else b) k = if c then andThen a k else andThen b k := by split <;> rfl

theorem finish_ite [Decidable c] (v : Bool) (a b : Option Flow) :
    finish v (if c then a else b) = if c then finish v a else finish v b := by split <;> rfl

theorem map_ite [Decidable c] (f : α → β) (a b : Option α) :
    Option.map f (if c then a else b) = if c then Option.map f a else Option.map f b := by split <;> rfl

theorem bind_ite [Decidable c] (f : α → Option β) (a b : Option α) :
    Option.bind (if c then a else b) f = if c then Option.bind a f else Option.bind b f := by split <;> rfl

/-- `cxx_agree [the model's and the tree's names]`: unfold both, and compare. -/
macro "cxx_agree" "[" names:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [Cxx.call, Cxx.andThen_go, Cxx.andThen_back, Cxx.andThen_none, Cxx.finish_back, Cxx.finish_go, Cxx.finish_none,
      Cxx.exec_skip, Cxx.exec_seq, Cxx.exec_block, Cxx.exec_set, Cxx.exec_decl, Cxx.exec_ite, Cxx.exec_ret_none, Cxx.exec_ret_some,
      Cxx.assign, Cxx.leave_go, Cxx.leave_back, Cxx.leave_none, Cxx.leave_ite, Cxx.Ty.ofWord, Cxx.eval, Cxx.cond, Cxx.Store.get, Cxx.Store.has,
      Cxx.Store.set, Cxx.Val.cmp, Cxx.Val.bin, Cxx.Val.conv, Cxx.CmpOp.on, Cxx.BinOp.on, Cxx.andThen_ite, Cxx.finish_ite,
      Cxx.map_ite, Cxx.bind_ite, $names,*])

/-! The tree, written back as the words it was read from. -/

def BinOp.word : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .and => "&" | .or => "|" | .xor => "^"

def CmpOp.word : CmpOp → String
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">=" | .eq => "==" | .ne => "!="

def Expr.tokens : Expr → List String
  | .lit n => [toString n]
  | .name x => [x]
  | .conv _ e => e.tokens
  | .bin op a b => a.tokens ++ [op.word] ++ b.tokens
  | .cmp op a b => a.tokens ++ [op.word] ++ b.tokens
  | .paren e => ["("] ++ e.tokens ++ [")"]
  | .truth b => [if b then "true" else "false"]

def Stmt.tokens : Stmt → List String
  | .skip => []
  | .seq a b => a.tokens ++ b.tokens
  | .block s => ["{"] ++ s.tokens ++ ["}"]
  | .set x e => [x, "="] ++ e.tokens ++ [";"]
  | .ite c t hasElse e => ["if", "("] ++ c.tokens ++ [")"] ++ t.tokens ++ (if hasElse then ["else"] ++ e.tokens else [])
  | .decl type x e => [type, x, "="] ++ e.tokens ++ [";"]
  | .forLoop init c x e body => ["for", "("] ++ init.tokens ++ c.tokens ++ [";", x, "="] ++ e.tokens ++ [")"] ++ body.tokens
  | .whileLoop c body => ["while", "("] ++ c.tokens ++ [")"] ++ body.tokens
  | .ret none => ["return", ";"]
  | .ret (some e) => ["return"] ++ e.tokens ++ [";"]

end Cxx
