import ClerkOwed

/-! The proofs about Clerk: a DRAFT by draft.py. Nothing here is trusted, and nothing here says
what is owed: that is `Clerk.Owed`, generated from the class. Each statement was tried by one
automatic proof; a statement it did not close is `sorry`, marked LEFT, which the audit refuses. -/

set_option maxHeartbeats 400000

namespace Clerk
namespace Claims

theorem stamp_safe : ∀ (me : Clerk) (world : Nat → BitVec 64), Clerk.Inv me → (Clerk.stamp me world).isSome := by
  intros; simp_all [Clerk.Inv, Clerk.raw, Clerk.stamp, Clerk.note, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem stamp_inv : ∀ (me : Clerk) (world : Nat → BitVec 64) (me' : Clerk) (r : BitVec 8), Clerk.Inv me → Clerk.stamp me world = some (me', r) → Clerk.Inv me' := by
  intros; simp_all [Clerk.Inv, Clerk.raw, Clerk.stamp, Clerk.note, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem note_safe : ∀ (me : Clerk), Clerk.Inv me → (Clerk.note me).isSome := by
  intros; simp_all [Clerk.Inv, Clerk.raw, Clerk.stamp, Clerk.note, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem note_inv : ∀ (me : Clerk) (me' : Clerk) (r : BitVec 64), Clerk.Inv me → Clerk.note me = some (me', r) → Clerk.Inv me' := by
  intros; simp_all [Clerk.Inv, Clerk.raw, Clerk.stamp, Clerk.note, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

/-- Everything owed. -/
theorem owed : Clerk.Owed :=
  { stamp_safe, stamp_inv, note_safe, note_inv }

end Claims
end Clerk
