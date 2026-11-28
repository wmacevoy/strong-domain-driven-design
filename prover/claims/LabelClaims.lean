import LabelOwed

/-! The proofs about Label: a DRAFT by draft.py. Nothing here is trusted, and nothing here says
what is owed: that is `Label.Owed`, generated from the class. Each statement was tried by one
automatic proof; a statement it did not close is `sorry`, marked LEFT, which the audit refuses. -/

set_option maxHeartbeats 400000

namespace Label
namespace Claims

theorem new_v_safe : ∀ (v : BitVec 64), (Label.new_v v).isSome := by
  intros; simp_all [Label.Inv, Label.raw, Label.new_v, Label.new_s, Label.number, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.bytesOf, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_v_inv : ∀ (v : BitVec 64) (me : Label), Label.new_v v = some me → Label.Inv me := by
  intros; simp_all [Label.Inv, Label.raw, Label.new_v, Label.new_s, Label.number, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.bytesOf, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_s_safe : ∀ (s : Prooc.Bytes), (Label.new_s s).isSome := by
  intros; simp_all [Label.Inv, Label.raw, Label.new_v, Label.new_s, Label.number, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.bytesOf, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_s_inv : ∀ (s : Prooc.Bytes) (me : Label), Label.new_s s = some (.gave me) → Label.Inv me := by
  intros; simp_all [Label.Inv, Label.raw, Label.new_v, Label.new_s, Label.number, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.bytesOf, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem number_safe : ∀ (me : Label), Label.Inv me → (Label.number me).isSome := by
  intros; simp_all [Label.Inv, Label.raw, Label.new_v, Label.new_s, Label.number, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.bytesOf, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem number_same : ∀ (me : Label) (me' : Label) (r : BitVec 64), Label.number me = some (me', r) → me' = me := by
  intros; simp_all [Label.Inv, Label.raw, Label.new_v, Label.new_s, Label.number, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.bytesOf, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

/-- Everything owed. -/
theorem owed : Label.Owed :=
  { new_v_safe, new_v_inv, new_s_safe, new_s_inv, number_safe, number_same }

end Claims
end Label
