import OpenerOwed

/-! The proofs about Opener: a DRAFT by draft.py. Nothing here is trusted, and nothing here says
what is owed: that is `Opener.Owed`, generated from the class. Each statement was tried by one
automatic proof; a statement it did not close is `sorry`, marked LEFT, which the audit refuses. -/

set_option maxHeartbeats 400000

namespace Opener
namespace Claims

theorem new_safe : Opener.new.isSome := by
  intros; simp_all [Opener.Inv, Opener.raw, Opener.new, Opener.«open», Opener.again, Opener.count, Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.bytesOf, Prooc.fill, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.Bytes.ofArray, Prooc.span, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem new_inv : ∀ (me : Opener), Opener.new = some me → Opener.Inv me := by
  intros; simp_all [Opener.Inv, Opener.raw, Opener.new, Opener.«open», Opener.again, Opener.count, Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.bytesOf, Prooc.fill, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.Bytes.ofArray, Prooc.span, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem open_safe : ∀ (me : Opener) (p : Prooc.Bytes), Opener.Inv me → (Opener.«open» me p).isSome := by
  intro me p _
  have hs := Prooc.Bytes.size_toNat p
  have e : (8#64).toNat = 8 := rfl
  have e' : (8#32).toNat = 8 := rfl
  have hsomeSub : ∀ j n, j + n ≤ p.bytes.size → (Prooc.Bytes.sub p j n).isSome :=
    fun j n h => by simp [Prooc.Bytes.sub, h]
  have hsub : ∀ (j n : Nat) (q : Prooc.Bytes), Prooc.Bytes.sub p j n = some q → q.bytes.size = n := by
    intro j n q h
    unfold Prooc.Bytes.sub at h
    split at h
    · rename_i hle
      cases h
      show (p.bytes.extract j (j + n)).size = n
      simp only [Array.size_extract]
      omega
    · cases h
  have hnew : ∀ s : Prooc.Bytes, s.bytes.size = 8 → (Mark.new_s s).isSome := by
    intro s hsz
    have hne : Prooc.Bytes.size s = 8#64 := by
      rw [Prooc.Bytes.size_eq, hsz]; decide
    simp [Mark.new_s, hne, Prooc.fill, Prooc.copyIn, hsz]
  unfold Opener.«open»
  by_cases h : Prooc.Bytes.size p < 8#64
  · simp [h]
  · rw [if_neg h]
    rw [BitVec.lt_def, hs] at h
    have h8 : 8 ≤ p.bytes.size := by simp at h; omega
    have hle : (8#64) ≤ Prooc.Bytes.size p := by
      rw [BitVec.le_def, hs]; simpa using h8
    have hsz : ((Prooc.Bytes.size p) - 8#64).toNat = p.bytes.size - 8 := by
      rw [BitVec.toNat_sub_of_le hle, hs, e]
    simp only [e, e', hsz]
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hsomeSub 0 8 (by omega))
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hsomeSub 8 (p.bytes.size - 8) (by omega))
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (hnew q (hsub 0 8 q hq))
    cases m <;> simp [hq, hm, hr]

theorem open_inv : ∀ (me : Opener) (p : Prooc.Bytes) (me' : Opener) (r : Prooc.Outcome (Unit)), Opener.Inv me → Opener.«open» me p = some (me', r) → Opener.Inv me' := by
  intros; simp_all [Opener.Inv, Opener.raw, Opener.new, Opener.«open», Opener.again, Opener.count, Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.bytesOf, Prooc.fill, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.Bytes.ofArray, Prooc.span, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem again_safe : ∀ (me : Opener) (n : BitVec 64), Opener.Inv me → (Opener.again me n).isSome := by
  intros; simp_all [Opener.Inv, Opener.raw, Opener.new, Opener.«open», Opener.again, Opener.count, Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.bytesOf, Prooc.fill, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.Bytes.ofArray, Prooc.span, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem again_inv : ∀ (me : Opener) (n : BitVec 64) (me' : Opener) (r : Prooc.Outcome (Unit)), Opener.Inv me → Opener.again me n = some (me', r) → Opener.Inv me' := by
  intros; simp_all [Opener.Inv, Opener.raw, Opener.new, Opener.«open», Opener.again, Opener.count, Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.bytesOf, Prooc.fill, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.Bytes.ofArray, Prooc.span, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem count_safe : ∀ (me : Opener), Opener.Inv me → (Opener.count me).isSome := by
  intros; simp_all [Opener.Inv, Opener.raw, Opener.new, Opener.«open», Opener.again, Opener.count, Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.bytesOf, Prooc.fill, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.Bytes.ofArray, Prooc.span, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

theorem count_same : ∀ (me : Opener) (me' : Opener) (r : BitVec 64), Opener.count me = some (me', r) → me' = me := by
  intros; simp_all [Opener.Inv, Opener.raw, Opener.new, Opener.«open», Opener.again, Opener.count, Mark.Inv, Mark.raw, Mark.new_s, Mark.new_b, Mark.«at», Prooc.get, Prooc.set, Prooc.shl, Prooc.shr, Prooc.div, Prooc.mod, Prooc.sadd, Prooc.ssub, Prooc.copyIn, Prooc.copyOwn, Prooc.bytesOf, Prooc.fill, Prooc.Bytes.read, Prooc.Bytes.sub, Prooc.Bytes.ofArray, Prooc.span, Prooc.outside, Prooc.pick, Prooc.Bytes.size_toNat, Prooc.Bytes.size_eq, BitVec.lt_def, BitVec.le_def] <;> (try split) <;> (try split at *) <;> grind

/-- Everything owed. -/
theorem owed : Opener.Owed :=
  { new_safe, new_inv, open_safe, open_inv, again_safe, again_inv, count_safe, count_same }

end Claims
end Opener
