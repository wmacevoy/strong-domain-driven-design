import bounded_checked_ofOwed

/-! The proofs about bounded_checked_of. Nothing here is trusted, and nothing here says what is
owed: that is `bounded_checked_of.Owed`, generated from the class template as it stands in its own
file, and `owed`, at the end, is a proof of it.

It is proved once, of every type T whose values compare and of every A and B. Its constructor
tests the number when the program runs, and the process ends if it is not within the bounds: so
one that exists is within them. -/

namespace bounded_checked_of
namespace Claims

variable {T : Type} [LE T] [DecidableLE T] [Inhabited T]

theorem new_safe (A B raw : T) : bounded_checked_of.new_pre A B raw → (bounded_checked_of.new A B raw).isSome := by
  intro h; simp [bounded_checked_of.new, h]

theorem new_inv (A B raw : T) (me : bounded_checked_of T) : bounded_checked_of.new A B raw = some me → bounded_checked_of.Inv A B me := by
  intro h
  by_cases hp : bounded_checked_of.new_pre A B raw
  · simp [bounded_checked_of.new, hp] at h
    subst h
    simpa [bounded_checked_of.Inv, bounded_checked_of.new_pre] using hp
  · simp [bounded_checked_of.new, hp] at h

theorem number_safe (A B : T) (me : bounded_checked_of T) : bounded_checked_of.Inv A B me → (bounded_checked_of.number A B me).isSome := by
  intro _; simp [bounded_checked_of.number]

theorem number_same (A B : T) (me me' : bounded_checked_of T) (r : T) : bounded_checked_of.number A B me = some (me', r) → me' = me := by
  intro h; simp [bounded_checked_of.number] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : bounded_checked_of.Owed :=
  { new_safe := new_safe, new_inv := new_inv, number_safe := number_safe, number_same := number_same }

end Claims
end bounded_checked_of
