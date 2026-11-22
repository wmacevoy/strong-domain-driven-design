import JarOwed

/-! The proofs about Jar. Nothing here is trusted: `Jar.Owed`, generated from the class, says what
is owed, and `owed` is a proof of it. -/

namespace Jar
namespace Claims

theorem new_safe : Jar.new.isSome := by simp [Jar.new]

theorem new_inv : ∀ (me : Jar), Jar.new = some me → Inv me := by
  intro me h; simp [Jar.new] at h; subst h; simp [Inv]

theorem add_safe : ∀ (me : Jar) (n : BitVec 32), Inv me → (Jar.add me n).isSome := by
  intro me n _; simp only [Jar.add]; split <;> simp

theorem add_inv : ∀ (me : Jar) (n : BitVec 32) (me' : Jar) (r : Unit), Inv me → Jar.add me n = some (me', r) → Inv me' := by
  intro me n me' r hinv h
  simp only [Jar.add] at h
  split at h <;> simp at h <;> rw [← h] <;> simp only [Inv] at * <;> bv_omega

theorem count_safe : ∀ (me : Jar), Inv me → (Jar.count me).isSome := by
  intro me _; simp [Jar.count]

theorem count_same : ∀ (me me' : Jar) (r : BitVec 32), Jar.count me = some (me', r) → me' = me := by
  intro me me' r h; simp [Jar.count] at h; exact h.1.symm

theorem roomFor_safe : ∀ (me : Jar) (n : BitVec 32), Inv me → (Jar.roomFor me n).isSome := by
  intro me n _; simp only [Jar.roomFor]; split <;> simp

theorem roomFor_same : ∀ (me : Jar) (n : BitVec 32) (me' : Jar) (r : BitVec 32), Jar.roomFor me n = some (me', r) → me' = me := by
  intro me n me' r h; simp only [Jar.roomFor] at h; split at h <;> simp at h <;> exact h.1.symm

/-- Everything owed. -/
theorem owed : Jar.Owed := { new_safe, new_inv, add_safe, add_inv, count_safe, count_same, roomFor_safe, roomFor_same }

end Claims
end Jar
