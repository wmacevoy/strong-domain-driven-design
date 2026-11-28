import GatherOwed

/-! The proofs about Gather: a DRAFT by draft.py. Nothing here is trusted, and nothing here says
what is owed: that is `Gather.Owed`, generated from the class. Each statement was tried by one
automatic proof; a statement it did not close is `sorry`, marked LEFT, which the audit refuses. -/

set_option maxHeartbeats 400000

namespace Gather
namespace Claims

theorem new_safe : Gather.new.isSome := by
  intros; simp_all [Gather.Inv, Gather.raw, Gather.new, Gather.gather, Gather.size, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_inv : ∀ (me : Gather), Gather.new = some me → Gather.Inv me := by
  intros; simp_all [Gather.Inv, Gather.raw, Gather.new, Gather.gather, Gather.size, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem gather_safe : ∀ (me : Gather) (world : Nat → BitVec 64), Gather.Inv me → (Gather.gather me world).isSome := by
  intros; simp_all [Gather.Inv, Gather.raw, Gather.new, Gather.gather, Gather.size, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem gather_inv : ∀ (me : Gather) (world : Nat → BitVec 64) (me' : Gather) (r : BitVec 8), Gather.Inv me → Gather.gather me world = some (me', r) → Gather.Inv me' := by
  intros; simp_all [Gather.Inv, Gather.raw, Gather.new, Gather.gather, Gather.size, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem size_safe : ∀ (me : Gather), Gather.Inv me → (Gather.size me).isSome := by
  intros; simp_all [Gather.Inv, Gather.raw, Gather.new, Gather.gather, Gather.size, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem size_same : ∀ (me : Gather) (me' : Gather) (r : BitVec 64), Gather.size me = some (me', r) → me' = me := by
  intros; simp_all [Gather.Inv, Gather.raw, Gather.new, Gather.gather, Gather.size, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

/-- Everything owed. -/
theorem owed : Gather.Owed :=
  { new_safe, new_inv, gather_safe, gather_inv, size_safe, size_same }

end Claims
end Gather
