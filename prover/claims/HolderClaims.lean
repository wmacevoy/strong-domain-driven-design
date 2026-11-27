import HolderOwed

/-! The proofs about Holder: a DRAFT by draft.py. Nothing here is trusted, and nothing here says
what is owed: that is `Holder.Owed`, generated from the class. Each statement was tried by one
automatic proof; a statement it did not close is `sorry`, marked LEFT, which the audit refuses. -/

set_option maxHeartbeats 400000

namespace Holder
namespace Claims

theorem new_safe : Holder.new.isSome := by
  intros; simp_all [Holder.Inv, Holder.raw, Holder.new, Holder.hold, Holder.size, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.Bytes.read, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_inv : ∀ (me : Holder), Holder.new = some me → Holder.Inv me := by
  intros; simp_all [Holder.Inv, Holder.raw, Holder.new, Holder.hold, Holder.size, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.Bytes.read, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem hold_safe : ∀ (me : Holder) (p : Prooc.Bytes), Holder.Inv me → (Holder.hold me p).isSome := by
  intros; simp_all [Holder.Inv, Holder.raw, Holder.new, Holder.hold, Holder.size, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.Bytes.read, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem hold_inv : ∀ (me : Holder) (p : Prooc.Bytes) (me' : Holder) (r : BitVec 8), Holder.Inv me → Holder.hold me p = some (me', r) → Holder.Inv me' := by
  intro me p me' r hinv h
  simp only [Holder.hold] at h
  split at h
  · simp at h
    obtain ⟨rfl, -⟩ := h
    exact hinv
  · rename_i hc
    generalize hcp : Prooc.copyIn me.held 0 p 0 (Prooc.Bytes.size p).toNat = c at h
    cases c with
    | none => simp at h
    | some v =>
      simp at h
      obtain ⟨rfl, -⟩ := h
      simp only [Holder.Inv]
      bv_omega

theorem size_safe : ∀ (me : Holder), Holder.Inv me → (Holder.size me).isSome := by
  intros; simp_all [Holder.Inv, Holder.raw, Holder.new, Holder.hold, Holder.size, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.Bytes.read, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem size_same : ∀ (me : Holder) (me' : Holder) (r : BitVec 64), Holder.size me = some (me', r) → me' = me := by
  intros; simp_all [Holder.Inv, Holder.raw, Holder.new, Holder.hold, Holder.size, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.Bytes.read, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

/-- Everything owed. -/
theorem owed : Holder.Owed :=
  { new_safe, new_inv, hold_safe, hold_inv, size_safe, size_same }

end Claims
end Holder
