import BitsOwed

/-! The proofs about Bits. Nothing here is trusted, and nothing here says what is owed: that is
`Bits.Owed` (BitsOwed.lean, generated from the class), and `owed`, at the end, is a proof of it. -/

namespace Bits
namespace Claims

/-- Why each shift is defined: a number's low six bits are a number below 64. -/
theorem amount_lt (n : BitVec 64) : n.toNat &&& 63 < 64 := by
  have h := @Nat.and_le_right n.toNat 63
  omega

theorem new_safe : Bits.new.isSome := by
  simp [Bits.new]

theorem new_inv : ∀ (me : Bits), Bits.new = some me → Inv me := by
  intro me _; simp [Inv]

theorem put_safe : ∀ (me : Bits) (n : BitVec 64), Inv me → (Bits.put me n).isSome := by
  intro me n _
  simp [Bits.put, Prooc.shl, amount_lt]

theorem put_inv : ∀ (me : Bits) (n : BitVec 64) (me' : Bits) (r : Unit),
    Inv me → Bits.put me n = some (me', r) → Inv me' := by
  intro me n me' r _ _; simp [Inv]

theorem has_safe : ∀ (me : Bits) (n : BitVec 64), Inv me → (Bits.has me n).isSome := by
  intro me n _
  simp [Bits.has, Prooc.shr, amount_lt]

theorem has_same : ∀ (me : Bits) (n : BitVec 64) (me' : Bits) (r : BitVec 64),
    Bits.has me n = some (me', r) → me' = me := by
  intro me n me' r h
  simp [Bits.has, Prooc.shr, amount_lt] at h
  exact h.1.symm

/-- Everything owed. -/
theorem owed : Bits.Owed :=
  { new_safe, new_inv, put_safe, put_inv, has_safe, has_same }

end Claims
end Bits
