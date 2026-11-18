import bounded_checked_ofOwed

/-! The proofs about bounded_checked_of, of gosh's `src/meetup/bounded.h`. Nothing here is trusted, and nothing here says what is
owed: that is `bounded_checked_of.Owed`, generated from the class template as it stands in its own
file, and `owed`, at the end, is a proof of it.

It is proved once, of every type T whose values compare and of every A and B. Its constructor
expects nothing: it tests, and `good` says what the test found. So where `good` is said, the
number is within the bounds. -/

namespace bounded_checked_of
namespace Claims

variable {T : Type} [LE T] [DecidableLE T] [Inhabited T]

theorem new_safe (A B raw : T) : (bounded_checked_of.new A B raw).isSome := by
  simp [bounded_checked_of.new]

theorem new_inv (A B raw : T) (me : bounded_checked_of T) : bounded_checked_of.new A B raw = some me → bounded_checked_of.Inv A B me := by
  intro h
  simp [bounded_checked_of.new] at h
  subst h
  by_cases hp : A ≤ raw ∧ raw ≤ B
  · simp [bounded_checked_of.Inv, hp]
  · simp [bounded_checked_of.Inv, hp]

theorem ok_safe (A B : T) (me : bounded_checked_of T) : bounded_checked_of.Inv A B me → (bounded_checked_of.ok A B me).isSome := by
  intro _; simp [bounded_checked_of.ok]

theorem ok_same (A B : T) (me me' : bounded_checked_of T) (r : BitVec 8) : bounded_checked_of.ok A B me = some (me', r) → me' = me := by
  intro h; simp [bounded_checked_of.ok] at h; exact h.1.symm

theorem number_safe (A B : T) (me : bounded_checked_of T) : bounded_checked_of.Inv A B me → bounded_checked_of.number_pre A B me → (bounded_checked_of.number A B me).isSome := by
  intro _ hp; simp [bounded_checked_of.number, hp]

theorem number_same (A B : T) (me me' : bounded_checked_of T) (r : T) : bounded_checked_of.number A B me = some (me', r) → me' = me := by
  intro h
  by_cases hp : bounded_checked_of.number_pre A B me
  · simp [bounded_checked_of.number, hp] at h; exact h.1.symm
  · simp [bounded_checked_of.number, hp] at h

/-- Everything owed. -/
theorem owed : bounded_checked_of.Owed :=
  { new_safe := new_safe, new_inv := new_inv, ok_safe := ok_safe, ok_same := ok_same,
    number_safe := number_safe, number_same := number_same }

end Claims
end bounded_checked_of
