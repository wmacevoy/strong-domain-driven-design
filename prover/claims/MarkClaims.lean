import MarkOwed

/-! The proofs about Mark: a DRAFT by draft.py. Nothing here is trusted, and nothing here says
what is owed: that is `Mark.Owed`, generated from the class. Each statement was tried by one
automatic proof; a statement it did not close is `sorry`, marked LEFT, which the audit refuses. -/

set_option maxHeartbeats 400000

namespace Mark
namespace Claims

theorem new_safe : ∀ (s : Prooc.Bytes), (Mark.new s).isSome := by
  intros; simp_all [Mark.Inv, Mark.raw, Mark.new, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.fill, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_inv : ∀ (s : Prooc.Bytes) (me : Mark), Mark.new s = some (.gave me) → Mark.Inv me := by
  intros; simp_all [Mark.Inv, Mark.raw, Mark.new, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.fill, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem at_safe : ∀ (me : Mark) (i : BitVec 64), Mark.Inv me → (Mark.«at» me i).isSome := by
  intros; simp_all [Mark.Inv, Mark.raw, Mark.new, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.fill, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem at_same : ∀ (me : Mark) (i : BitVec 64) (me' : Mark) (r : BitVec 32), Mark.«at» me i = some (me', r) → me' = me := by
  intros; simp_all [Mark.Inv, Mark.raw, Mark.new, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.fill, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

/-- Everything owed. -/
theorem owed : Mark.Owed :=
  { new_safe, new_inv, at_safe, at_same }

end Claims
end Mark
