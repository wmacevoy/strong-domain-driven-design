import StunAnswerOwed

/-! The proofs about StunAnswer. Nothing here is trusted, and nothing here says what is owed: that
is `StunAnswer.Owed` (StunAnswerOwed.lean, generated from the class), and `owed`, at the end, is a
proof of it. -/

namespace StunAnswer
namespace Claims

/-! The loops inside a round: each ends within 17 rounds, commits no memory error, and changes
only the address. -/

theorem loop3_done (fuel left : Nat) (me : StunAnswer) (data : Prooc.Bytes) (body : BitVec 64)
    (found : BitVec 32) («at» : BitVec 64) (type : BitVec 32) (size v : BitVec 64)
    (port6 zeros b0 b1 b10 b11 j : BitVec 32) (fam : BitVec 32) (hf : me.family = fam) (hl : 16 - j.toNat < left) :
    Prooc.DoneWith (parse.loop3 fuel left me data body found «at» type size v port6 zeros b0 b1 b10 b11 j)
      (fun s => s.1.family = fam) := by
  induction left generalizing me j with
  | zero => omega
  | succ left ih =>
    unfold parse.loop3
    by_cases h : j < 16#32
    · have hlt : j.toNat < 16 := by bv_omega
      simp (disch := omega) [parse.round3, h, Prooc.set_of_lt]
      exact ih _ _ hf (by bv_omega)
    · simp [parse.round3, h, hf]

theorem loop5_done (fuel left : Nat) (me : StunAnswer) (data : Prooc.Bytes) (body : BitVec 64)
    (found : BitVec 32) («at» : BitVec 64) (type : BitVec 32) (size v : BitVec 64)
    (port4 a0 a1 a2 a3 m : BitVec 32) (fam : BitVec 32) (hf : me.family = fam) (hl : 16 - m.toNat < left) :
    Prooc.DoneWith (parse.loop5 fuel left me data body found «at» type size v port4 a0 a1 a2 a3 m)
      (fun s => s.1.family = fam) := by
  induction left generalizing me m with
  | zero => omega
  | succ left ih =>
    unfold parse.loop5
    by_cases h : m < 16#32
    · have hlt : m.toNat < 16 := by bv_omega
      simp (disch := omega) [parse.round5, h, Prooc.set_of_lt]
      exact ih _ _ hf (by bv_omega)
    · simp [parse.round5, h, hf]

/-- Byte `k` of an IPv6 address as the answer gives it: the value's byte, undisguised with the header's. -/
def W (data : Prooc.Bytes) (v k : BitVec 64) : BitVec 8 :=
  BitVec.setWidth 8 (BitVec.setWidth 32 (data.byte (v + 4#64 + k).toNat) ^^^ BitVec.setWidth 32 (data.byte (4#64 + k).toNat))

/-- The loop that copies an IPv6 address: with the 20 bytes of the value inside the view, it is
done, and the first two bytes kept are the first two of the answer's. -/
theorem loop4_done (fuel left : Nat) (me : StunAnswer) (data : Prooc.Bytes) (body : BitVec 64)
    (found : BitVec 32) («at» : BitVec 64) (type : BitVec 32) (size v : BitVec 64)
    (port6 zeros b0 b1 b10 b11 : BitVec 32) (k : BitVec 64) (fam : BitVec 32) (hf : me.family = fam)
    (hv : v.toNat + 20 ≤ data.bytes.size) (hl : 16 - k.toNat < left)
    (h0 : 1 ≤ k.toNat → me.addr[0] = W data v 0#64) (h1 : 2 ≤ k.toNat → me.addr[1] = W data v 1#64) :
    Prooc.DoneWith (parse.loop4 fuel left me data body found «at» type size v port6 zeros b0 b1 b10 b11 k)
      (fun s => s.1.family = fam ∧ s.1.addr[0] = W data v 0#64 ∧ s.1.addr[1] = W data v 1#64) := by
  have hs := data.small
  induction left generalizing me k with
  | zero => omega
  | succ left ih =>
    unfold parse.loop4
    by_cases h : k < 16#64
    · have hlt : k.toNat < 16 := by bv_omega
      simp (disch := omega) [parse.round4, h, Prooc.set_of_lt, Prooc.Bytes.read_of_lt]
      refine ih _ _ ?_ ?_ ?_ ?_
      · exact hf
      · bv_omega
      · intro _
        by_cases hk : k = 0#64
        · subst hk; simp [W]
        · have : k.toNat ≠ 0 := by bv_omega
          simp [this]
          exact h0 (by omega)
      · intro hk2
        by_cases hk : k = 1#64
        · subst hk; simp [W]
        · have : k.toNat ≠ 1 := by bv_omega
          simp [this]
          exact h1 (by bv_omega)
    · have hge : 16 ≤ k.toNat := by bv_omega
      simp [parse.round4, h, hf]
      exact ⟨h0 (by omega), h1 (by omega)⟩

/-- The loop that looks for ten zero bytes: with the 20 bytes of the value inside the view. -/
theorem loop2_done (fuel left : Nat) (me : StunAnswer) (data : Prooc.Bytes) (body : BitVec 64)
    (found : BitVec 32) («at» : BitVec 64) (type : BitVec 32) (size v : BitVec 64)
    (port6 zeros : BitVec 32) (i : BitVec 64)
    (hv : v.toNat + 20 ≤ data.bytes.size) (hl : 10 - i.toNat < left) :
    Prooc.DoneWith (parse.loop2 fuel left me data body found «at» type size v port6 zeros i)
      (fun _ => True) := by
  have hs := data.small
  induction left generalizing zeros i with
  | zero => omega
  | succ left ih =>
    unfold parse.loop2
    by_cases h : i < 10#64
    · have hlt : i.toNat < 10 := by bv_omega
      simp (disch := omega) [parse.round2, h, Prooc.Bytes.read_of_lt]
      split
      · exact ih _ _ (by bv_omega)
      · exact ih _ _ (by bv_omega)
    · simp [parse.round2, h]

/-! The branches: each has a result and keeps the invariant, given that the value it reads is
inside the view. `fuel` of 17 is enough for the loops inside them. -/

theorem block2_ok (fuel : Nat) (me : StunAnswer) (data : Prooc.Bytes) (body : BitVec 64)
    (found : BitVec 32) («at» : BitVec 64) (type : BitVec 32) (size v : BitVec 64)
    (port6 zeros b0 b1 b10 b11 : BitVec 32) (hfuel : 17 ≤ fuel) (hv : v.toNat + 20 ≤ data.bytes.size) :
    Prooc.Ok (parse.block2 fuel me data body found «at» type size v port6 zeros b0 b1 b10 b11)
      (fun s => Inv s.1) := by
  have hs := data.small
  unfold parse.block2
  simp (disch := omega) [Prooc.Bytes.read_of_lt, Prooc.set_of_lt]
  apply Prooc.ok_bind_done (Q := fun s => s.1.family = 4#32)
  · apply loop3_done <;> first | rfl | assumption | omega | (simp; omega) | simp
  · intro s hq
    obtain ⟨me', j'⟩ := s
    simp_all [Inv]

/-- Why what was tested is what is kept: the test is on 32-bit numbers, the bytes kept are their
low 8 bits, and the invariant reads those as 32-bit numbers again. -/
theorem back (x y : BitVec 8) :
    BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 y))
      = BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 y := by
  ext i; simp

theorem block3_ok (fuel : Nat) (me : StunAnswer) (data : Prooc.Bytes) (body : BitVec 64)
    (found : BitVec 32) («at» : BitVec 64) (type : BitVec 32) (size v : BitVec 64)
    (port6 zeros b0 b1 b10 b11 : BitVec 32) (hfuel : 17 ≤ fuel) (hv : v.toNat + 20 ≤ data.bytes.size)
    (hnl : ¬ (BitVec.setWidth 32 (W data v 0#64) = 254#32 ∧ BitVec.setWidth 32 (W data v 1#64) &&& 192#32 = 128#32)) :
    Prooc.Ok (parse.block3 fuel me data body found «at» type size v port6 zeros b0 b1 b10 b11)
      (fun s => Inv s.1) := by
  have hs := data.small
  unfold parse.block3
  simp (disch := omega)
  apply Prooc.ok_bind_done (Q := fun s => s.1.family = 6#32 ∧ s.1.addr[0] = W data v 0#64 ∧ s.1.addr[1] = W data v 1#64)
  · apply loop4_done <;> first | rfl | assumption | omega | (simp; omega) | simp
  · intro s hq
    obtain ⟨me', k'⟩ := s
    obtain ⟨hfam, ha0, ha1⟩ := hq
    simp only [Prooc.ok_some, Inv]
    simp at hfam ha0 ha1
    refine ⟨Or.inr hfam, fun h => hnl ?_⟩
    rw [← ha0, ← ha1]
    exact ⟨h.1.2, h.2⟩

theorem block1_ok (fuel : Nat) (me : StunAnswer) (data : Prooc.Bytes) (body : BitVec 64)
    (found : BitVec 32) («at» : BitVec 64) (type : BitVec 32) (size v : BitVec 64)
    (hfuel : 17 ≤ fuel) (hv : v.toNat + 20 ≤ data.bytes.size) (hinv : Inv me) :
    Prooc.Ok (parse.block1 fuel me data body found «at» type size v) (fun s => Inv s.1) := by
  have hs := data.small
  unfold parse.block1
  simp (disch := omega) [Prooc.Bytes.read_of_lt]
  apply Prooc.ok_bind_done (Q := fun _ => True)
  · apply loop2_done <;> first | rfl | assumption | omega | (simp; omega) | simp
  · intro s _
    obtain ⟨zeros', i'⟩ := s
    simp (disch := omega)
    split
    · apply Prooc.ok_bind (Q := fun s => Inv s.1)
      · apply block2_ok <;> assumption
      · intro s hq; simpa using hq
    · split
      · rename_i _ hll
        apply Prooc.ok_bind (Q := fun s => Inv s.1)
        · apply block3_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfuel hv
          intro h
          simp only [W, back] at h
          exact hll (by simpa using h.1) (by simpa using h.2)
        · intro s hq; simpa using hq
      · simpa using hinv

theorem block4_ok (fuel : Nat) (me : StunAnswer) (data : Prooc.Bytes) (body : BitVec 64)
    (found : BitVec 32) («at» : BitVec 64) (type : BitVec 32) (size v : BitVec 64)
    (hfuel : 17 ≤ fuel) (hv : v.toNat + 8 ≤ data.bytes.size) :
    Prooc.Ok (parse.block4 fuel me data body found «at» type size v) (fun s => Inv s.1) := by
  have hs := data.small
  unfold parse.block4
  simp (disch := omega) [Prooc.Bytes.read_of_lt, Prooc.set_of_lt, parse.block5]
  split <;>
  · apply Prooc.ok_bind_done (Q := fun s => s.1.family = 4#32)
    · apply loop5_done <;> first | rfl | assumption | omega | (simp; omega) | simp
    · intro s hq
      obtain ⟨me', m'⟩ := s
      simp_all [Inv]

/-! The loop over the attributes. -/

/-- What a round hands on: the invariant, and where the next attribute begins. -/
def RoundPost (body «at» : BitVec 64) : Prooc.Step (StunAnswer × BitVec 32 × BitVec 64) (StunAnswer × BitVec 8) → Prop
  | .done s => Inv s.1
  | .next s => Inv s.1 ∧ «at».toNat + 4 ≤ s.2.2.toNat ∧ s.2.2.toNat ≤ 20 + body.toNat + 3
  | .ret _ => False

theorem size_small (a b : BitVec 8) : (BitVec.setWidth 64 a <<< 8 ||| BitVec.setWidth 64 b) < 65536#64 := by
  have ha := a.isLt
  have hb := b.isLt
  have h1 : (BitVec.setWidth 64 a <<< 8).toNat < 2 ^ 16 := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have h2 : (BitVec.setWidth 64 b).toNat < 2 ^ 16 := by simp; omega
  have := Nat.or_lt_two_pow h1 h2
  simp only [BitVec.lt_def, BitVec.toNat_or]
  simpa using this

/-- A number is the sum of its bits outside a mask and its bits inside it. -/
theorem split_at (x m : BitVec 64) : x = (x &&& ~~~m) + (x &&& m) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i; simp; cases x[i] <;> cases m[i] <;> simp
  · ext i; simp; cases x[i] <;> cases m[i] <;> simp

/-- Padding to 4 bytes adds at most 3, and takes nothing away. -/
theorem pad_bounds (size : BitVec 64) (h : size < 65536#64) :
    size ≤ (size + 3#64 &&& 18446744073709551612#64) ∧ (size + 3#64 &&& 18446744073709551612#64) ≤ size + 3#64 := by
  generalize hx : size + 3#64 = x
  have hsplit := split_at x 3#64
  have hm : ~~~3#64 = 18446744073709551612#64 := by decide
  rw [hm] at hsplit
  have hq : (x &&& 3#64).toNat ≤ 3 := by
    simp only [BitVec.toNat_and]; exact Nat.and_le_right
  have hp : (x &&& 18446744073709551612#64).toNat ≤ x.toNat := by
    simp only [BitVec.toNat_and]; exact Nat.and_le_left
  generalize (x &&& 18446744073709551612#64) = p at *
  generalize (x &&& 3#64) = q at *
  bv_omega

theorem round1_ok (fuel : Nat) (me : StunAnswer) (data : Prooc.Bytes) (body : BitVec 64) (found : BitVec 32) («at» : BitVec 64)
    (hfuel : 17 ≤ fuel) (hbody : 20 + body.toNat ≤ data.bytes.size)
    (hat : «at».toNat ≤ 20 + body.toNat + 3) (hinv : Inv me) :
    Prooc.Ok (parse.round1 fuel me data body found «at») (RoundPost body «at») := by
  have hs := data.small
  unfold parse.round1
  by_cases c1 : «at» + 4#64 ≤ 20#64 + body
  · have c1' : «at».toNat + 4 ≤ 20 + body.toNat := by bv_omega
    simp (disch := omega) [c1, Prooc.Bytes.read_of_lt]
    have hsz := size_small (data.byte ((«at».toNat + 2) % 18446744073709551616)) (data.byte ((«at».toNat + 3) % 18446744073709551616))
    generalize (BitVec.setWidth 64 (data.byte ((«at».toNat + 2) % 18446744073709551616)) <<< 8 ||| BitVec.setWidth 64 (data.byte ((«at».toNat + 3) % 18446744073709551616))) = size at hsz ⊢
    generalize (BitVec.setWidth 32 (data.byte «at».toNat) <<< 8 ||| BitVec.setWidth 32 (data.byte ((«at».toNat + 1) % 18446744073709551616))) = type
    have hpad := pad_bounds size hsz
    generalize (size + 3#64 &&& 18446744073709551612#64) = pad at hpad ⊢
    by_cases cb : 20#64 + body < «at» + 4#64 + size
    · simp [cb, RoundPost, hinv]
    · simp only [cb, ite_false]
      have hb2 : «at».toNat + 4 + size.toNat ≤ 20 + body.toNat := by bv_omega
      have second : ∀ (me' : StunAnswer) (found' : BitVec 32), Inv me' →
          Prooc.Ok
            (Option.bind
              (Option.bind
                (if (type = 32#32 ∨ type = 1#32) ∧ 8#64 ≤ size then
                  Option.bind (data.read ((«at».toNat + 4 + 1) % 18446744073709551616))
                    (fun l => some (decide (BitVec.setWidth 32 l = 1#32)))
                else some false)
                (fun l => if l = true then some (!decide (found' = 1#32) || !decide (type = 1#32)) else some false))
              (fun l =>
                if l = true then
                  Option.bind (parse.block4 fuel me' data body found' «at» type size («at» + 4#64))
                    (fun x => some (Prooc.Step.next (x.fst, x.snd, «at» + 4#64 + pad)))
                else some (Prooc.Step.next (me', found', «at» + 4#64 + pad))))
            (RoundPost body «at») := by
        intro me' found' hi
        by_cases cD : (type = 32#32 ∨ type = 1#32) ∧ 8#64 ≤ size
        · have h8 : size.toNat ≥ 8 := by bv_omega
          simp (disch := omega) [cD, Prooc.Bytes.read_of_lt]
          split
          · simp only [Option.bind_some]
            split
            · apply Prooc.ok_bind (Q := fun s => Inv s.1)
              · apply block4_ok <;> first | assumption | bv_omega
              · intro s hq
                simp [RoundPost, hq]
                bv_omega
            · simp [RoundPost, hi]
              bv_omega
          · simp [RoundPost, hi]
            bv_omega
        · simp [cD, RoundPost, hi]
          bv_omega
      by_cases cA : type = 32#32 ∧ 20#64 ≤ size
      · have h20 : size.toNat ≥ 20 := by bv_omega
        simp (disch := omega) [cA, Prooc.Bytes.read_of_lt]
        split
        · apply Prooc.ok_bind (Q := fun s => Inv s.1)
          · apply block1_ok <;> first | assumption | bv_omega
          · intro s hq
            simpa (disch := omega) [cA, Prooc.Bytes.read_of_lt] using second s.1 s.2 hq
        · simpa (disch := omega) [cA, Prooc.Bytes.read_of_lt] using second me found hinv
      · simp only [cA, ite_false]
        simpa using second me found hinv
  · simp [c1, RoundPost, hinv]

/-- The loop over the attributes is done within a round for every 4 bytes of the body, and two more. -/
theorem loop1_ok (fuel left : Nat) (me : StunAnswer) (data : Prooc.Bytes) (body : BitVec 64)
    (found : BitVec 32) («at» : BitVec 64) (hfuel : 17 ≤ fuel) (hbody : 20 + body.toNat ≤ data.bytes.size)
    (hat : «at».toNat ≤ 20 + body.toNat + 3) (hinv : Inv me)
    (hl : 20 + body.toNat + 8 - «at».toNat < 4 * left) :
    Prooc.DoneWith (parse.loop1 fuel left me data body found «at») (fun s => Inv s.1) := by
  induction left generalizing me found «at» with
  | zero => omega
  | succ left ih =>
    unfold parse.loop1
    obtain ⟨r, hr, hpost⟩ := round1_ok fuel me data body found «at» hfuel hbody hat hinv
    rw [hr]
    cases r with
    | next s =>
      obtain ⟨me', found', at'⟩ := s
      simp only [RoundPost] at hpost
      simp
      exact ih me' found' at' hpost.2.2 hpost.1 (by omega)
    | done s => simpa [RoundPost] using hpost
    | ret r => simp [RoundPost] at hpost

/-- How many rounds are enough for any loop of `parse`: a hint, which nothing owed names. -/
def parse_rounds (_me : StunAnswer) (data : Prooc.Bytes) : Nat := data.bytes.size + 20

/-- `parse` has a result, whatever the bytes and however many, and keeps the invariant. -/
theorem parse_ok (me : StunAnswer) (data : Prooc.Bytes) (hinv : Inv me) :
    Prooc.Ok (parse (parse_rounds me data) me data) (fun s => Inv s.1) := by
  have hs := data.small
  have hlen := Prooc.Bytes.size_toNat data
  unfold parse parse_rounds
  by_cases c0 : Prooc.Bytes.size data < 20#64
  · simp [c0, hinv]
  · have h20 : 20 ≤ data.bytes.size := by bv_omega
    simp (disch := omega) [c0, Prooc.Bytes.read_of_lt]
    have hsz := size_small (data.byte 2) (data.byte 3)
    generalize (BitVec.setWidth 64 (data.byte 2) <<< 8 ||| BitVec.setWidth 64 (data.byte 3)) = body at hsz ⊢
    repeat' (first | split | simp only [Option.bind_some])
    all_goals first
      | (simp [hinv]; done)
      | (apply Prooc.ok_bind_done (Q := fun s => Inv s.1)
         · apply loop1_ok <;> first | assumption | bv_omega | (simp; bv_omega)
         · intro s hq
           obtain ⟨me', found', at'⟩ := s
           simpa using hq)

/-! What is owed (StunAnswerOwed.lean). -/

theorem new_safe : StunAnswer.new.isSome := by
  simp (disch := omega) [StunAnswer.new, Prooc.set_of_lt]

theorem new_inv : ∀ (me : StunAnswer), StunAnswer.new = some me → Inv me := by
  intro me h
  simp (disch := omega) [StunAnswer.new, Prooc.set_of_lt] at h
  subst h
  simp [Inv]

theorem parse_ends : ∀ (me : StunAnswer) (data : Prooc.Bytes), Inv me →
    ∃ (fuel : Nat) (me' : StunAnswer) (r : BitVec 8), StunAnswer.parse fuel me data = some (me', r) ∧ Inv me' := by
  intro me data hinv
  obtain ⟨⟨me', r⟩, hs, hi⟩ := parse_ok me data hinv
  exact ⟨parse_rounds me data, me', r, hs, hi⟩

theorem kept_family_safe : ∀ (me : StunAnswer), Inv me → (StunAnswer.kept_family me).isSome := by
  intro me _; simp [StunAnswer.kept_family]

theorem kept_family_same : ∀ (me me' : StunAnswer) (r : BitVec 32), StunAnswer.kept_family me = some (me', r) → me' = me := by
  intro me me' r h; simp [StunAnswer.kept_family] at h; exact h.1.symm

theorem kept_port_safe : ∀ (me : StunAnswer), Inv me → (StunAnswer.kept_port me).isSome := by
  intro me _; simp [StunAnswer.kept_port]

theorem kept_port_same : ∀ (me me' : StunAnswer) (r : BitVec 32), StunAnswer.kept_port me = some (me', r) → me' = me := by
  intro me me' r h; simp [StunAnswer.kept_port] at h; exact h.1.symm

theorem kept_byte_safe : ∀ (me : StunAnswer) (i : BitVec 32), Inv me → (StunAnswer.kept_byte me i).isSome := by
  intro me i _
  simp [StunAnswer.kept_byte]
  split
  · simp
  · have hi : i.toNat < 16 := by bv_omega
    simp [Prooc.get_of_lt, hi]

theorem kept_byte_same : ∀ (me : StunAnswer) (i : BitVec 32) (me' : StunAnswer) (r : BitVec 32),
    StunAnswer.kept_byte me i = some (me', r) → me' = me := by
  intro me i me' r h
  simp [StunAnswer.kept_byte] at h
  split at h
  · simp at h; exact h.1.symm
  · have hi : i.toNat < 16 := by bv_omega
    simp [Prooc.get_of_lt, hi] at h
    exact h.1.symm

/-- Everything owed. -/
theorem owed : StunAnswer.Owed :=
  { new_safe, new_inv, parse_ends, kept_family_safe, kept_family_same, kept_port_safe, kept_port_same,
    kept_byte_safe, kept_byte_same }

end Claims
end StunAnswer
