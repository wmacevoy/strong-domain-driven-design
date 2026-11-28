import MarkOwed

/-! The proofs about Mark: a DRAFT by draft.py. Nothing here is trusted, and nothing here says
what is owed: that is `Mark.Owed`, generated from the class. Each statement was tried by one
automatic proof; a statement it did not close is `sorry`, marked LEFT, which the audit refuses. -/

set_option maxHeartbeats 400000

namespace Mark
namespace Claims

theorem new_s_safe : ∀ (s : Prooc.Bytes), (Mark.new_s s).isSome := by
  intros; simp_all [Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.fill, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_s_inv : ∀ (s : Prooc.Bytes) (me : Mark), Mark.new_s s = some (.gave me) → Mark.Inv me := by
  intros; simp_all [Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.fill, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_b_safe : ∀ (b : BitVec 32), (Mark.new_b b).isSome := by
  intros; simp_all [Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.fill, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_b_inv : ∀ (b : BitVec 32) (me : Mark), Mark.new_b b = some me → Mark.Inv me := by
  intros; simp_all [Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.fill, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem at_safe : ∀ (me : Mark) (i : BitVec 64), Mark.Inv me → (Mark.«at» me i).isSome := by
  intros; simp_all [Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.fill, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem at_same : ∀ (me : Mark) (i : BitVec 64) (me' : Mark) (r : BitVec 32), Mark.«at» me i = some (me', r) → me' = me := by
  intros; simp_all [Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.fill, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

/-- Everything owed. -/
theorem owed : Mark.Owed :=
  { new_s_safe, new_s_inv, new_b_safe, new_b_inv, at_safe, at_same }

end Claims
end Mark
