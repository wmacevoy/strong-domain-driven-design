import MeterOwed

/-! The proofs about Meter: a DRAFT by draft.py. Nothing here is trusted, and nothing here says
what is owed: that is `Meter.Owed`, generated from the class. Each statement was tried by one
automatic proof; a statement it did not close is `sorry`, marked LEFT, which the audit refuses. -/

set_option maxHeartbeats 400000

namespace Meter
namespace Claims

theorem new_safe : Meter.new.isSome := by
  intros; simp_all [Meter.Inv, Meter.raw, Meter.new, Meter.add, Meter.value, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_inv : ∀ (me : Meter), Meter.new = some me → Meter.Inv me := by
  intros; simp_all [Meter.Inv, Meter.raw, Meter.new, Meter.add, Meter.value, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem add_safe : ∀ (me : Meter) (n : BitVec 32), Meter.Inv me → (Meter.add me n).isSome := by
  intros; simp_all [Meter.Inv, Meter.raw, Meter.new, Meter.add, Meter.value, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem add_inv : ∀ (me : Meter) (n : BitVec 32) (me' : Meter) (r : BitVec 32), Meter.Inv me → Meter.add me n = some (me', r) → Meter.Inv me' := by
  intros; simp_all [Meter.Inv, Meter.raw, Meter.new, Meter.add, Meter.value, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem value_safe : ∀ (me : Meter), Meter.Inv me → (Meter.value me).isSome := by
  intros; simp_all [Meter.Inv, Meter.raw, Meter.new, Meter.add, Meter.value, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem value_same : ∀ (me : Meter) (me' : Meter) (r : BitVec 32), Meter.value me = some (me', r) → me' = me := by
  intros; simp_all [Meter.Inv, Meter.raw, Meter.new, Meter.add, Meter.value, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.read, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

/-- Everything owed. -/
theorem owed : Meter.Owed :=
  { new_safe, new_inv, add_safe, add_inv, value_safe, value_same }

end Claims
end Meter
