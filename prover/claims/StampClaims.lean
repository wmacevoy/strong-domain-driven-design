import StampOwed

/-! The proofs about Stamp: a DRAFT by draft.py. Nothing here is trusted, and nothing here says
what is owed: that is `Stamp.Owed`, generated from the class. Each statement was tried by one
automatic proof; a statement it did not close is `sorry`, marked LEFT, which the audit refuses. -/

set_option maxHeartbeats 400000

namespace Stamp
namespace Claims

theorem new_safe : Stamp.new.isSome := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_inv : ∀ (me : Stamp), Stamp.new = some me → Stamp.Inv me := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem keep_safe : ∀ (me : Stamp) (p : Prooc.Bytes) («at» : BitVec 64), Stamp.Inv me → (Stamp.keep me p «at»).isSome := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem keep_inv : ∀ (me : Stamp) (p : Prooc.Bytes) («at» : BitVec 64) (me' : Stamp) (r : BitVec 8), Stamp.Inv me → Stamp.keep me p «at» = some (me', r) → Stamp.Inv me' := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem keep_tail_safe : ∀ (me : Stamp) (s : Prooc.Bytes), Stamp.Inv me → (Stamp.keep_tail me s).isSome := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem keep_tail_inv : ∀ (me : Stamp) (s : Prooc.Bytes) (me' : Stamp) (r : Unit), Stamp.Inv me → Stamp.keep_tail me s = some (me', r) → Stamp.Inv me' := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem clear_safe : ∀ (me : Stamp) (n : BitVec 64), Stamp.Inv me → (Stamp.clear me n).isSome := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem clear_inv : ∀ (me : Stamp) (n : BitVec 64) (me' : Stamp) (r : BitVec 8), Stamp.Inv me → Stamp.clear me n = some (me', r) → Stamp.Inv me' := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem fold_safe : ∀ (me : Stamp), Stamp.Inv me → (Stamp.fold me).isSome := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem fold_inv : ∀ (me : Stamp) (me' : Stamp) (r : Unit), Stamp.Inv me → Stamp.fold me = some (me', r) → Stamp.Inv me' := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem first_safe : ∀ (me : Stamp), Stamp.Inv me → (Stamp.first me).isSome := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem first_same : ∀ (me : Stamp) (me' : Stamp) (r : BitVec 32), Stamp.first me = some (me', r) → me' = me := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem count_safe : ∀ (me : Stamp), Stamp.Inv me → (Stamp.count me).isSome := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem count_same : ∀ (me : Stamp) (me' : Stamp) (r : BitVec 64), Stamp.count me = some (me', r) → me' = me := by
  intros; simp_all [Stamp.Inv, Stamp.raw, Stamp.new, Stamp.keep, Stamp.keep_tail, Stamp.clear, Stamp.fold, Stamp.first, Stamp.count, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

/-- Everything owed. -/
theorem owed : Stamp.Owed :=
  { new_safe, new_inv, keep_safe, keep_inv, keep_tail_safe, keep_tail_inv, clear_safe, clear_inv, fold_safe, fold_inv, first_safe, first_same, count_safe, count_same }

end Claims
end Stamp
