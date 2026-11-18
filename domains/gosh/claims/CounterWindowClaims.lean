import CounterWindowOwed

/-! The proofs about CounterWindow. Nothing here is trusted, and nothing here says what is owed:
that is `CounterWindow.Owed` (CounterWindowOwed.lean, generated from the class), and `owed`, at
the end, is a proof of it. -/

namespace CounterWindow
namespace Claims

/-- Why every read and write of `seen` is inside it: a counter's low ten bits, less the low six,
are a number below 16. -/
theorem word_lt (c : BitVec 64) : (c.toNat &&& 1023) >>> 6 < 16 := by
  have h := @Nat.and_le_right c.toNat 1023
  simp only [Nat.shiftRight_eq_div_pow]
  omega

/-- Why every shift is defined: a counter's low six bits are a number below 64. -/
theorem bit_lt (c : BitVec 64) : c.toNat &&& 63 < 64 := by
  have h := @Nat.and_le_right c.toNat 63
  omega

/-- The loop that forgets the counters between the old top and the new is done within 1025 rounds,
however far apart they are: each round `i - top` is one more, and past 1024 it stops. It changes
nothing but `seen`. -/
theorem loop1_done (fuel left : Nat) (me : CounterWindow) (c one i : BitVec 64)
    (hl : 1025 - (i - me.top).toNat < left) :
    Prooc.DoneWith (take.loop1 fuel left me c one i) (fun s => s.1.any = me.any) := by
  induction left generalizing me i with
  | zero => omega
  | succ left ih =>
    unfold take.loop1
    by_cases h : (i ≤ c) ∧ ((i - me.top) ≤ 1024#64)
    · simp [take.round1, h, Prooc.get, Prooc.set, Prooc.shl, word_lt, bit_lt]
      exact ih _ _ (by simp; bv_omega)
    · simp [take.round1, h]

theorem new_safe : CounterWindow.new.isSome := by
  simp [CounterWindow.new, Prooc.set]

theorem new_inv : ∀ (me : CounterWindow), CounterWindow.new = some me → Inv me := by
  intro me h
  simp [CounterWindow.new, Prooc.set] at h
  subst h
  simp [Inv]

theorem take_ends : ∀ (me : CounterWindow) (c : BitVec 64), Inv me →
    ∃ (fuel : Nat) (me' : CounterWindow) (r : BitVec 8),
      CounterWindow.take fuel me c = some (me', r) ∧ Inv me' := by
  intro me c hinv
  refine ⟨1026, ?_⟩
  by_cases h0 : (me.any).setWidth 32 = 0#32
  · simp [CounterWindow.take, h0, Prooc.set, Inv]
  · by_cases h1 : c > me.top
    · obtain ⟨s, hs, hany⟩ := loop1_done 1026 1026 me c 1#64 (me.top + 1#64) (by omega)
      simp [CounterWindow.take, h0, h1, hs, Prooc.get, Prooc.set, Prooc.shl, word_lt, bit_lt, Inv, hany]
      exact hinv
    · by_cases h2 : me.top - c ≥ 1024#64
      · simp [CounterWindow.take, h0, h1, h2]
        exact hinv
      · simp [CounterWindow.take, h0, h1, h2, Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, word_lt, bit_lt]
        split <;> simp [Inv] <;> exact hinv

/-- Everything owed. -/
theorem owed : CounterWindow.Owed :=
  { new_safe, new_inv, take_ends }

end Claims
end CounterWindow
