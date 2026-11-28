import InboxOwed

/-! The proofs about Inbox: a DRAFT by draft.py. Nothing here is trusted, and nothing here says
what is owed: that is `Inbox.Owed`, generated from the class. Each statement was tried by one
automatic proof; a statement it did not close is `sorry`, marked LEFT, which the audit refuses. -/

set_option maxHeartbeats 400000

namespace Inbox
namespace Claims

theorem new_safe : Inbox.new.isSome := by
  intros; simp_all [Inbox.Inv, Inbox.raw, Inbox.new, Inbox.keep, Inbox.«at», bounded_of.Inv, bounded_of.raw, bounded_of.new_pre, bounded_of.new, bounded_of.number, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.bytesOf, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.Bytes.ofArray, Prooc.span, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_inv : ∀ (me : Inbox), Inbox.new = some me → Inbox.Inv me := by
  intros; simp_all [Inbox.Inv, Inbox.raw, Inbox.new, Inbox.keep, Inbox.«at», bounded_of.Inv, bounded_of.raw, bounded_of.new_pre, bounded_of.new, bounded_of.number, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.bytesOf, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.Bytes.ofArray, Prooc.span, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem keep_safe : ∀ (me : Inbox) (p : Prooc.Bytes), Inbox.Inv me → 0#64 ≤ Prooc.Bytes.size p ∧ Prooc.Bytes.size p ≤ 64#64 → (Inbox.keep me p).isSome := by
  intros; simp_all [Inbox.Inv, Inbox.raw, Inbox.new, Inbox.keep, Inbox.«at», bounded_of.Inv, bounded_of.raw, bounded_of.new_pre, bounded_of.new, bounded_of.number, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.bytesOf, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.Bytes.ofArray, Prooc.span, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem keep_inv : ∀ (me : Inbox) (p : Prooc.Bytes) (me' : Inbox) (r : Unit), Inbox.Inv me → 0#64 ≤ Prooc.Bytes.size p ∧ Prooc.Bytes.size p ≤ 64#64 → Inbox.keep me p = some (me', r) → Inbox.Inv me' := by
  -- by hand (the agent, 2026-11-28): the automatic proof did not close it
  intro me p me' r _ ⟨_, h⟩ hk
  simp only [Inbox.keep, Inbox.Inv] at hk ⊢
  cases hc : Prooc.copyIn me.held 0 p 0 (Prooc.Bytes.size p).toNat <;> simp_all
  obtain ⟨-, rfl⟩ := hk; exact h

theorem at_safe : ∀ (me : Inbox) (i : BitVec 64), Inbox.Inv me → (Inbox.«at» me i).isSome := by
  intros; simp_all [Inbox.Inv, Inbox.raw, Inbox.new, Inbox.keep, Inbox.«at», bounded_of.Inv, bounded_of.raw, bounded_of.new_pre, bounded_of.new, bounded_of.number, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.bytesOf, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.Bytes.ofArray, Prooc.span, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem at_same : ∀ (me : Inbox) (i : BitVec 64) (me' : Inbox) (r : BitVec 32), Inbox.«at» me i = some (me', r) → me' = me := by
  intros; simp_all [Inbox.Inv, Inbox.raw, Inbox.new, Inbox.keep, Inbox.«at», bounded_of.Inv, bounded_of.raw, bounded_of.new_pre, bounded_of.new, bounded_of.number, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.bytesOf, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.Bytes.ofArray, Prooc.span, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

/-- Everything owed. -/
theorem owed : Inbox.Owed :=
  { new_safe, new_inv, keep_safe, keep_inv, at_safe, at_same }

end Claims
end Inbox
