import CounterWindowOwed

/-! The proofs about CounterWindow. Nothing here is trusted, and nothing here says what is owed:
that is `CounterWindow.Owed` (CounterWindowOwed.lean, generated from gosh's class as it stands),
and `owed`, at the end, is a proof of it. -/

namespace CounterWindow
namespace Claims

/-- Why every read and write of `seen` is inside it: a counter's remainder by 1024, divided by 64,
is a number below 16. -/
theorem word_lt (c : BitVec 64) : c.toNat % 1024 / 64 < 16 := by omega

/-- Why every shift is defined: a counter's remainder by 64 is below 64. -/
theorem bit_lt (c : BitVec 64) : c.toNat % 64 < 64 := by omega

/-- `clear` has a result, and changes nothing but `seen`. -/
theorem clear_ok (me : CounterWindow) (c : BitVec 64) :
    Prooc.Ok (CounterWindow.clear me c) (fun s => s.1.any = me.any ∧ s.1.top = me.top) := by
  simp [CounterWindow.clear, Prooc.get, Prooc.set, Prooc.shl, word_lt, bit_lt]

/-- `set` has a result, and changes nothing but `seen`. -/
theorem set_ok (me : CounterWindow) (c : BitVec 64) :
    Prooc.Ok (CounterWindow.set me c) (fun s => s.1.any = me.any ∧ s.1.top = me.top) := by
  simp [CounterWindow.set, Prooc.get, Prooc.set, Prooc.shl, word_lt, bit_lt]

/-- `test` has a result. -/
theorem test_ok (me : CounterWindow) (c : BitVec 64) : (CounterWindow.test me c).isSome := by
  simp [CounterWindow.test, Prooc.get, Prooc.shr, word_lt, bit_lt]

/-- The loop that forgets the counters between the old top and the new is done within 1025 rounds,
however far apart they are: each round `i - top` is one more, and past 1024 it stops. -/
theorem loop1_done (fuel left : Nat) (me : CounterWindow) (c i : BitVec 64)
    (hl : 1025 - (i - me.top).toNat < left) :
    Prooc.DoneWith (take.loop1 fuel left me c i) (fun _ => True) := by
  induction left generalizing me i with
  | zero => omega
  | succ left ih =>
    unfold take.loop1
    by_cases h : (i ≤ c) ∧ ((i - me.top) ≤ 1024#64)
    · obtain ⟨s, hs, _, htop⟩ := clear_ok me i
      simp [take.round1, h, hs]
      exact ih _ _ (by rw [htop]; bv_omega)
    · simp [take.round1, h]

theorem new_safe : CounterWindow.new.isSome := by
  simp [CounterWindow.new]

theorem new_inv : ∀ (me : CounterWindow), CounterWindow.new = some me → Inv me := by
  intro me _; simp [Inv]

theorem take_ends : ∀ (me : CounterWindow) (c : BitVec 64), Inv me →
    ∃ (fuel : Nat) (me' : CounterWindow) (r : BitVec 8),
      CounterWindow.take fuel me c = some (me', r) ∧ Inv me' := by
  intro me c _
  refine ⟨1026, ?_⟩
  simp only [Inv, and_true]
  by_cases h0 : me.any ≠ 0#8
  · by_cases h1 : c > me.top
    · obtain ⟨s, hs, _⟩ := loop1_done 1026 1026 me c (me.top + 1#64) (by omega)
      obtain ⟨t, ht, _⟩ := set_ok { s.1 with top := c } c
      simp [CounterWindow.take, h0, h1, hs, ht]
    · obtain ⟨t, ht, _⟩ := set_ok me c
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (test_ok me c)
      by_cases h2 : me.top - c ≥ 1024#64
      · simp [CounterWindow.take, h0, h1, h2]
      · simp [CounterWindow.take, h0, h1, h2, hu, ht]
        split <;> simp
  · simp [CounterWindow.take, h0]

/-- Everything owed. -/
theorem owed : CounterWindow.Owed :=
  { new_safe, new_inv, take_ends }

end Claims
end CounterWindow
