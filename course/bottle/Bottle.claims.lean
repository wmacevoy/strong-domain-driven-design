import BottleOwed

/-! Lesson 5: the proofs of what is owed of Bottle: that no method commits a memory error, and
that each keeps the invariant. Nothing here is trusted: `Bottle.Owed` (generated from the class,
gen/BottleOwed.lean) says what must be proved, and `owed`, at the end, is a proof of it, which the
audit and Lean's kernel check. Each proof opens the method (`simp [Bottle.setVolume]`), takes each
branch of its `if` (`split`), and leaves what is left, comparisons of 32-bit numbers, to `bv_omega`. -/

namespace Bottle
namespace Claims

theorem new_safe : Bottle.new.isSome := by
  simp [Bottle.new]

theorem new_inv : ∀ (me : Bottle), Bottle.new = some me → Inv me := by
  intro me h
  simp [Bottle.new] at h
  subst h
  simp [Inv]

theorem getVolume_safe : ∀ (me : Bottle), Inv me → (Bottle.getVolume me).isSome := by
  intro me _; simp [Bottle.getVolume]

theorem getVolume_same : ∀ (me me' : Bottle) (r : BitVec 32), Bottle.getVolume me = some (me', r) → me' = me := by
  intro me me' r h; simp [Bottle.getVolume] at h; exact h.1.symm

theorem getMaxVolume_safe : ∀ (me : Bottle), Inv me → (Bottle.getMaxVolume me).isSome := by
  intro me _; simp [Bottle.getMaxVolume]

theorem getMaxVolume_same : ∀ (me me' : Bottle) (r : BitVec 32), Bottle.getMaxVolume me = some (me', r) → me' = me := by
  intro me me' r h; simp [Bottle.getMaxVolume] at h; exact h.1.symm

theorem setVolume_safe : ∀ (me : Bottle) (value : BitVec 32), Inv me → (Bottle.setVolume me value).isSome := by
  intro me value _; simp [Bottle.setVolume]; split <;> simp

theorem setVolume_inv : ∀ (me : Bottle) (value : BitVec 32) (me' : Bottle) (r : Unit),
    Inv me → Bottle.setVolume me value = some (me', r) → Inv me' := by
  intro me value me' r _ h
  simp [Bottle.setVolume] at h
  split at h <;> simp at h <;> subst h <;> simp_all [Inv] <;> bv_omega

theorem setMaxVolume_safe : ∀ (me : Bottle) (value : BitVec 32), Inv me → (Bottle.setMaxVolume me value).isSome := by
  intro me value _; simp [Bottle.setMaxVolume]; split <;> simp

theorem setMaxVolume_inv : ∀ (me : Bottle) (value : BitVec 32) (me' : Bottle) (r : Unit),
    Inv me → Bottle.setMaxVolume me value = some (me', r) → Inv me' := by
  intro me value me' r _ h
  simp [Bottle.setMaxVolume] at h
  split at h <;> simp at h <;> subst h <;> simp_all [Inv] <;> bv_omega

/-- Everything owed. -/
theorem owed : Bottle.Owed :=
  { new_safe, new_inv, getVolume_safe, getVolume_same, getMaxVolume_safe, getMaxVolume_same,
    setVolume_safe, setVolume_inv, setMaxVolume_safe, setMaxVolume_inv }

end Claims
end Bottle
