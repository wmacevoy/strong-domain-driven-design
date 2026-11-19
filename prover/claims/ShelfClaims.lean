import ShelfOwed

/-! The proofs about Shelf. Nothing here is trusted, and nothing here says what is owed: that is
`Shelf.Owed`, generated from the class as it stands in its own file, and `owed`, at the end, is a
proof of it. `add` and `at` are proved given what they expect of their caller; `first` calls `at`,
and is proved with nothing given: so it is proved to call it rightly. -/

namespace Shelf
namespace Claims

theorem new_safe : Shelf.new.isSome := by
  simp [Shelf.new]

theorem new_inv : ∀ (me : Shelf), Shelf.new = some me → Inv me := by
  intro me h
  simp [Shelf.new] at h
  subst h
  simp [Inv]

theorem add_safe : ∀ (me : Shelf) (v : BitVec 32), Inv me → Shelf.add_pre me v → (Shelf.add me v).isSome := by
  intro me v _ hp
  have hu : me.used.toNat < 8 := by simp only [Shelf.add_pre] at hp; bv_omega
  simp [Shelf.add, hp, Prooc.set, hu]

theorem add_inv : ∀ (me : Shelf) (v : BitVec 32) (me' : Shelf) (r : Unit),
    Inv me → Shelf.add_pre me v → Shelf.add me v = some (me', r) → Inv me' := by
  intro me v me' r _ hp h
  have hu : me.used.toNat < 8 := by simp only [Shelf.add_pre] at hp; bv_omega
  simp [Shelf.add, hp, Prooc.set, hu] at h
  subst h
  simp only [Inv]
  bv_omega

theorem at_safe : ∀ (me : Shelf) (i : BitVec 32), Inv me → Shelf.at_pre me i → (Shelf.«at» me i).isSome := by
  intro me i hinv hp
  have hi : i.toNat < 8 := by simp only [Shelf.at_pre, Inv] at hp hinv; bv_omega
  simp [Shelf.«at», hp, Prooc.get, hi]

theorem at_same : ∀ (me : Shelf) (i : BitVec 32) (me' : Shelf) (r : BitVec 32),
    Shelf.«at» me i = some (me', r) → me' = me := by
  intro me i me' r h
  by_cases hp : Shelf.at_pre me i
  · simp only [Shelf.«at», hp] at h
    cases hg : Prooc.get me.slots i.toNat with
    | none => simp [hg] at h
    | some v => simp [hg] at h; exact h.1.symm
  · simp [Shelf.«at», hp] at h

/-- `first` asks `at` for place 0 only where a place is used: what `at` expects is kept. -/
theorem first_safe : ∀ (me : Shelf), Inv me → (Shelf.first me).isSome := by
  intro me hinv
  by_cases h0 : me.used = 0#32
  · simp [Shelf.first, h0]
  · have hp : Shelf.at_pre me 0#32 := by simp only [Shelf.at_pre]; bv_omega
    have hs := at_safe me 0#32 hinv hp
    cases hg : Shelf.«at» me 0#32 with
    | none => simp [hg] at hs
    | some v => simp [Shelf.first, h0, hg]

theorem first_same : ∀ (me me' : Shelf) (r : BitVec 32), Shelf.first me = some (me', r) → me' = me := by
  intro me me' r h
  by_cases h0 : me.used = 0#32
  · simp [Shelf.first, h0] at h; exact h.1.symm
  · cases hg : Shelf.«at» me 0#32 with
    | none => simp [Shelf.first, h0, hg] at h
    | some v =>
      have hsame := at_same me 0#32 v.1 v.2 hg
      simp [Shelf.first, h0, hg] at h
      exact h.1.symm

/-- Everything owed. -/
theorem owed : Shelf.Owed :=
  { new_safe, new_inv, add_safe, add_inv, at_safe, at_same, first_safe, first_same }

end Claims
end Shelf
