import KeeperOwed

/-! The proofs about Keeper: a DRAFT by draft.py. Nothing here is trusted, and nothing here says
what is owed: that is `Keeper.Owed`, generated from the class. Each statement was tried by one
automatic proof; a statement it did not close is `sorry`, marked LEFT, which the audit refuses. -/

set_option maxHeartbeats 400000

namespace Keeper
namespace Claims

theorem new_safe : Keeper.new.isSome := by
  intros; simp_all [Keeper.Inv, Keeper.raw, Keeper.new, Keeper.keep, Keeper.kept_count, Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_inv : ∀ (me : Keeper), Keeper.new = some me → Keeper.Inv me := by
  intros; simp_all [Keeper.Inv, Keeper.raw, Keeper.new, Keeper.keep, Keeper.kept_count, Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem keep_safe : ∀ (me : Keeper) (p : Prooc.Bytes), Keeper.Inv me → (Keeper.keep me p).isSome := by
  intros; simp_all [Keeper.Inv, Keeper.raw, Keeper.new, Keeper.keep, Keeper.kept_count, Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem keep_inv : ∀ (me : Keeper) (p : Prooc.Bytes) (me' : Keeper) (r : Prooc.Outcome (Unit)), Keeper.Inv me → Keeper.keep me p = some (me', r) → Keeper.Inv me' := by
  intro me p me' r hinv hk
  have hsmall := p.small
  have hmod : p.bytes.size % 18446744073709551616 = p.bytes.size := Nat.mod_eq_of_lt (by omega)
  have hrest : 8 ≤ p.bytes.size → (p.bytes.size + 18446744073709551608) % 18446744073709551616 = p.bytes.size - 8 := fun h => by omega
  have hA : 8 ≤ p.bytes.size → (p.bytes.extract 0 8).size = 8 := fun h => by simp only [Array.size_extract]; omega
  have hB : 8 ≤ p.bytes.size → (p.bytes.extract 8 (8 + (18446744073709551608 + p.bytes.size) % 18446744073709551616)).size = p.bytes.size - 8 := fun h => by simp only [Array.size_extract, hrest h]; omega
  unfold Keeper.keep at hk
  unfold Keeper.Inv at hinv ⊢
  dsimp only at hk
  split at hk
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, -⟩ := hk
    exact hinv
  · rename_i hlt
    have h8 : 8 ≤ p.bytes.size := by
      simp only [BitVec.lt_def, Prooc.Bytes.size_toNat, BitVec.toNat_ofNat] at hlt
      omega
    have hA' := hA h8
    have hB' := hB h8
    have hr := hrest h8
    have hc : 8 + (18446744073709551608 + p.bytes.size) % 18446744073709551616 ≤ p.bytes.size := by omega
    repeat' split at hk
    all_goals (simp_all [Mark.new_s, Mark.raw, Prooc.fill, Prooc.filled, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.Bytes.sub, Prooc.Bytes.size, Vector.getElem_ofFn, Prooc.Bytes.byte, hmod])
    all_goals (try omega)
    all_goals grind

theorem kept_count_safe : ∀ (me : Keeper), Keeper.Inv me → (Keeper.kept_count me).isSome := by
  intros; simp_all [Keeper.Inv, Keeper.raw, Keeper.new, Keeper.keep, Keeper.kept_count, Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem kept_count_same : ∀ (me : Keeper) (me' : Keeper) (r : BitVec 64), Keeper.kept_count me = some (me', r) → me' = me := by
  intros; simp_all [Keeper.Inv, Keeper.raw, Keeper.new, Keeper.keep, Keeper.kept_count, Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copied, Prooc.copyOwn, Prooc.copiedOwn, Prooc.fill, Prooc.filled, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

/-- Everything owed. -/
theorem owed : Keeper.Owed :=
  { new_safe, new_inv, keep_safe, keep_inv, kept_count_safe, kept_count_same }

end Claims
end Keeper
