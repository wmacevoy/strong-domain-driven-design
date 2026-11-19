import GaugeOwed

/-! The proofs about Gauge. Nothing here is trusted, and nothing here says what is owed: that is
`Gauge.Owed` (GaugeOwed.lean, generated from the class), and `owed`, at the end, is a proof of it. -/

namespace Gauge
namespace Claims

theorem new_safe : Gauge.new.isSome := by
  simp [Gauge.new]

theorem new_inv : ∀ (me : Gauge), Gauge.new = some me → Inv me := by
  intro me h
  simp [Gauge.new] at h
  subst h
  simp [Inv]

theorem get_safe : ∀ (me : Gauge), Inv me → (Gauge.get me).isSome := by
  intro me _; simp [Gauge.get]

theorem get_same : ∀ (me me' : Gauge) (r : BitVec 32), Gauge.get me = some (me', r) → me' = me := by
  intro me me' r h; simp [Gauge.get] at h; exact h.1.symm

theorem getLimit_safe : ∀ (me : Gauge), Inv me → (Gauge.getLimit me).isSome := by
  intro me _; simp [Gauge.getLimit]

theorem getLimit_same : ∀ (me me' : Gauge) (r : BitVec 32), Gauge.getLimit me = some (me', r) → me' = me := by
  intro me me' r h; simp [Gauge.getLimit] at h; exact h.1.symm

theorem set_safe : ∀ (me : Gauge) (value : BitVec 32), Inv me → (Gauge.set me value).isSome := by
  intro me value _; simp [Gauge.set]; split <;> simp

theorem set_inv : ∀ (me : Gauge) (value : BitVec 32) (me' : Gauge) (r : Unit),
    Inv me → Gauge.set me value = some (me', r) → Inv me' := by
  intro me value me' r _ h
  simp [Gauge.set] at h
  split at h <;> simp at h <;> subst h <;> simp_all [Inv] <;> bv_omega

theorem setLimit_safe : ∀ (me : Gauge) (value : BitVec 32), Inv me → (Gauge.setLimit me value).isSome := by
  intro me value _; simp [Gauge.setLimit]; split <;> simp

theorem setLimit_inv : ∀ (me : Gauge) (value : BitVec 32) (me' : Gauge) (r : Unit),
    Inv me → Gauge.setLimit me value = some (me', r) → Inv me' := by
  intro me value me' r _ h
  simp [Gauge.setLimit] at h
  split at h <;> simp at h <;> subst h <;> simp_all [Inv] <;> bv_omega

/-- Everything owed. -/
theorem owed : Gauge.Owed :=
  { new_safe, new_inv, get_safe, get_same, getLimit_safe, getLimit_same, set_safe, set_inv,
    setLimit_safe, setLimit_inv }

/-! What Gauge is FOR, beyond the invariant (not owed, and so not audited: a reader's to read). -/

/-- `set` stores the value, or the limit if the value is above it; and leaves the limit alone. -/
theorem set_clamps : ∀ (me : Gauge) (value : BitVec 32) (me' : Gauge),
    Gauge.set me value = some (me', ()) →
    me'.level = (if value > me.limit then me.limit else value) ∧ me'.limit = me.limit := by
  intro me value me' h
  simp [Gauge.set] at h
  split at h <;> simp at h <;> subst h <;> simp_all <;> intro _ <;> bv_omega

end Claims
end Gauge
