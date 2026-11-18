import bounded_ofOwed

/-! The proofs about bounded_of, gosh's `src/meetup/bounded.h`. Nothing here is trusted, and nothing here says what is owed: that
is `bounded_of.Owed`, generated from the class template as it stands in its own file, and `owed`,
at the end, is a proof of it.

It is proved once, of every type T whose values compare and of every A and B: nothing here asks
what `≤` is. What the constructor expects of its caller is, word for word, what the invariant
says; so a bounded number is within its bounds because whoever made it owed that it was. -/

namespace bounded_of
namespace Claims

variable {T : Type} [LE T] [DecidableLE T] [Inhabited T]

theorem new_safe (A B raw : T) : bounded_of.new_pre A B raw → (bounded_of.new A B raw).isSome := by
  intro h; simp [bounded_of.new, h]

theorem new_inv (A B raw : T) (me : bounded_of T) : bounded_of.new A B raw = some me → bounded_of.Inv A B me := by
  intro h
  by_cases hp : bounded_of.new_pre A B raw
  · simp [bounded_of.new, hp] at h
    subst h
    simpa [bounded_of.Inv, bounded_of.new_pre] using hp
  · simp [bounded_of.new, hp] at h

theorem number_safe (A B : T) (me : bounded_of T) : bounded_of.Inv A B me → (bounded_of.number A B me).isSome := by
  intro _; simp [bounded_of.number]

theorem number_same (A B : T) (me me' : bounded_of T) (r : T) : bounded_of.number A B me = some (me', r) → me' = me := by
  intro h; simp [bounded_of.number] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : bounded_of.Owed :=
  { new_safe := new_safe, new_inv := new_inv, number_safe := number_safe, number_same := number_same }

end Claims
end bounded_of
