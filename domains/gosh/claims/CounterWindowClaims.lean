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
theorem loop1_done (fuel left : Nat) (me : CounterWindow) (counter : bounded_of (BitVec 64)) (c i : BitVec 64)
    (hl : 1025 - (i - me.top).toNat < left) :
    Prooc.DoneWith (take.loop1 fuel left me counter c i) (fun s => s.1.any = me.any ∧ s.1.top = me.top) := by
  induction left generalizing me i with
  | zero => omega
  | succ left ih =>
    unfold take.loop1
    by_cases h : (i ≤ c) ∧ ((i - me.top) ≤ 1024#64)
    · obtain ⟨s, hs, hany, htop⟩ := clear_ok me i
      simp [take.round1, h, hs]
      have := ih s.1 (i + 1#64) (by rw [htop]; bv_omega)
      rw [hany, htop] at this
      exact this
    · simp [take.round1, h]

theorem new_safe : CounterWindow.new.isSome := by
  simp [CounterWindow.new]

theorem new_inv : ∀ (me : CounterWindow), CounterWindow.new = some me → Inv me := by
  intro me h
  simp [CounterWindow.new] at h
  subst h
  simp [Inv]

/-- What `take` is given is a MeetupCounter, a bounded number from 0 to 2^62 - 1, so at most 2^62 - 1: that is why the highest counter
taken stays one (the invariant). Its memory and its ending hold for any number. -/
theorem take_ends : ∀ (me : CounterWindow) (counter : bounded_of (BitVec 64)), Inv me → bounded_of.Inv 0#64 4611686018427387903#64 counter →
    ∃ (fuel : Nat) (me' : CounterWindow) (r : BitVec 8),
      CounterWindow.take fuel me counter = some (me', r) ∧ Inv me' := by
  intro me counter hinv hcounter
  refine ⟨1026, ?_⟩
  simp only [bounded_of.Inv] at hcounter
  generalize hc : counter.value = c at hcounter
  by_cases h0 : me.any ≠ 0#8
  · by_cases h1 : c > me.top
    · obtain ⟨s, hs, hsany, _⟩ := loop1_done 1026 1026 me counter c (me.top + 1#64) (by omega)
      obtain ⟨t, ht, htany, httop⟩ := set_ok { s.1 with top := c } c
      refine ⟨t.1, 1#8, ?_, ?_⟩
      · simp [CounterWindow.take, bounded_of.number, hc, h0, h1, hs, ht]
      · simp only [Inv]; right; rw [httop]; exact hcounter.2
    · obtain ⟨t, ht, htany, httop⟩ := set_ok me c
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (test_ok me c)
      have hkeep : Inv t.1 := by
        simp only [Inv] at hinv ⊢
        rw [htany, httop]; exact hinv
      by_cases h2 : me.top - c ≥ 1024#64
      · exact ⟨me, 0#8, by simp [CounterWindow.take, bounded_of.number, hc, h0, h1, h2], hinv⟩
      · by_cases h3 : u.2 ≠ 0#8
        · exact ⟨me, 0#8, by simp [CounterWindow.take, bounded_of.number, hc, h0, h1, h2, hu, h3], hinv⟩
        · exact ⟨t.1, 1#8, by simp [CounterWindow.take, bounded_of.number, hc, h0, h1, h2, hu, h3, ht], hkeep⟩
  · refine ⟨_, 1#8, by simp [CounterWindow.take, bounded_of.number, hc, h0]; rfl, ?_⟩
    simp only [Inv]; right; exact hcounter.2

/-- The way in for code that is not proved: a MeetupCounterChecked is within the bounds (its
invariant: making one is what tested, and the process ended there otherwise). So the MeetupCounter
`take_checked` makes of its number is made rightly, and `take` is given what it expects. -/
theorem take_checked_ends : ∀ (me : CounterWindow) (given : bounded_checked_of (BitVec 64)), Inv me →
    bounded_checked_of.Inv 0#64 4611686018427387903#64 given →
    ∃ (fuel : Nat) (me' : CounterWindow) (r : BitVec 8),
      CounterWindow.take_checked fuel me given = some (me', r) ∧ Inv me' := by
  intro me given hinv hg
  have hb : 0#64 ≤ given.value ∧ given.value ≤ 4611686018427387903#64 := by simpa [bounded_checked_of.Inv] using hg
  have hl : bounded_of.Inv 0#64 4611686018427387903#64 ({ value := given.value } : bounded_of (BitVec 64)) := by
    simpa [bounded_of.Inv] using hb
  obtain ⟨fuel, me', r, ht, hi⟩ := take_ends me { value := given.value } hinv hl
  refine ⟨fuel, me', r, ?_, hi⟩
  simp [CounterWindow.take_checked, bounded_checked_of.number, bounded_of.new, bounded_of.new_pre, hb, ht]

/-- Everything owed. -/
theorem owed : CounterWindow.Owed :=
  { new_safe, new_inv, take_ends, take_checked_ends }

end Claims
end CounterWindow
