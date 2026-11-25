import StationOwed
import WaterClaims
import TrayClaims

/-! The proofs about Station, which has-a a Water and a Tray. Nothing here is trusted, and nothing
here says what is owed: that is `Station.Owed`, generated from the class as it stands in its own
file, and `owed`, at the end, is a proof of it.

Each part was proved alone (`Water.Claims.owed`, `Tray.Claims.owed`). Here the station is proved
from what each part's methods do: that each part keeps its own invariant is had from the part's
proof, and what is the station's own is the rule that spans them. -/

namespace Station
namespace Claims

/-- The invariant, as plain arithmetic: each part's own, and the tray holds the drips of the shots. -/
theorem inv_iff (me : Station) :
    Inv me ↔ Water.Inv me.water ∧ Tray.Inv me.tray ∧ me.shots ≤ 4#32 ∧ me.tray.ml = me.shots * 10#32 := by
  have h4 : (40#32 / 10#32) = 4#32 := by decide
  simp only [Inv, Tray.held, h4]
  by_cases a : me.shots ≤ 4#32 <;> by_cases b : me.tray.ml = me.shots * 10#32 <;> simp [a, b]

theorem new_safe : Station.new.isSome := by
  simp [Station.new, Water.new, Tray.new]

theorem new_inv : ∀ (me : Station), Station.new = some me → Inv me := by
  intro me h
  simp [Station.new, Water.new, Tray.new] at h
  subst h
  rw [inv_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Water.Inv, Tray.Inv]

/-- A shot is pulled only where the tank has the water and the tray the room: so what each part
expects of its caller is kept. -/
theorem pull_safe : ∀ (me : Station), Inv me → (Station.pull me).isSome := by
  intro me hi
  rw [inv_iff] at hi
  obtain ⟨hw, ht, -, -⟩ := hi
  simp only [Water.Inv, Tray.Inv] at hw ht
  simp only [Station.pull, Water.level, Tray.room]
  by_cases a : me.water.ml < 30#32
  · simp [a]
  by_cases b : 40#32 - me.tray.ml < 10#32
  · simp [a, b]
  have hp : Water.take_pre me.water 30#32 := by simp only [Water.take_pre]; bv_omega
  have hq : Tray.add_pre me.tray 10#32 := by simp only [Tray.add_pre]; bv_omega
  simp [a, b, Water.take, Tray.add, hp, hq]

theorem pull_inv : ∀ (me : Station) (me' : Station) (r : BitVec 32),
    Inv me → Station.pull me = some (me', r) → Inv me' := by
  intro me me' r hi h
  rw [inv_iff] at hi ⊢
  obtain ⟨hw, ht, hs, hd⟩ := hi
  simp only [Station.pull, Water.level, Tray.room] at h
  by_cases a : me.water.ml < 30#32
  · simp [a] at h; obtain ⟨rfl, -⟩ := h; exact ⟨hw, ht, hs, hd⟩
  by_cases b : 40#32 - me.tray.ml < 10#32
  · simp [a, b] at h; obtain ⟨rfl, -⟩ := h; exact ⟨hw, ht, hs, hd⟩
  simp only [Water.Inv, Tray.Inv] at hw ht
  have hp : Water.take_pre me.water 30#32 := by simp only [Water.take_pre]; bv_omega
  have hq : Tray.add_pre me.tray 10#32 := by simp only [Tray.add_pre]; bv_omega
  simp [a, b, Water.take, Tray.add, hp, hq] at h
  obtain ⟨rfl, -⟩ := h
  simp only [Water.Inv, Tray.Inv]
  -- at most four shots: each case is plain numbers (omega reads `shots * 10` as not linear)
  have hk : me.shots = 0#32 ∨ me.shots = 1#32 ∨ me.shots = 2#32 ∨ me.shots = 3#32 ∨ me.shots = 4#32 := by
    bv_omega
  rcases hk with hk | hk | hk | hk | hk <;> simp [hk] at hd b ⊢ <;> (try refine ⟨?_, ?_, ?_⟩) <;> bv_omega

theorem emptyTray_safe : ∀ (me : Station), Inv me → (Station.emptyTray me).isSome := by
  intro me _; simp [Station.emptyTray, Tray.empty]

theorem emptyTray_inv : ∀ (me : Station) (me' : Station) (r : Unit),
    Inv me → Station.emptyTray me = some (me', r) → Inv me' := by
  intro me me' r hi h
  rw [inv_iff] at hi ⊢
  simp [Station.emptyTray, Tray.empty] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨hi.1, by simp [Tray.Inv], by simp, by simp⟩

theorem refill_safe : ∀ (me : Station), Inv me → (Station.refill me).isSome := by
  intro me _; simp [Station.refill, Water.fill]

theorem refill_inv : ∀ (me : Station) (me' : Station) (r : Unit),
    Inv me → Station.refill me = some (me', r) → Inv me' := by
  intro me me' r hi h
  rw [inv_iff] at hi ⊢
  simp [Station.refill, Water.fill] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨by simp [Water.Inv], hi.2.1, hi.2.2.1, hi.2.2.2⟩

theorem pulled_safe : ∀ (me : Station), Inv me → (Station.pulled me).isSome := by
  intro me _; simp [Station.pulled]

theorem pulled_same : ∀ (me me' : Station) (r : BitVec 32), Station.pulled me = some (me', r) → me' = me := by
  intro me me' r h; simp [Station.pulled] at h; exact h.1.symm

/-- Everything owed. -/
theorem owed : Station.Owed :=
  { new_safe, new_inv, pull_safe, pull_inv, emptyTray_safe, emptyTray_inv, refill_safe, refill_inv,
    pulled_safe, pulled_same }

end Claims
end Station
