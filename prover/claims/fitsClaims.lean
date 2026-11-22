import fitsOwed

/-! The proofs about fits, a function. Nothing here is trusted: `fits.Owed`, generated from the
function, says what is owed, and `owed` is a proof of it. -/

namespace fits
namespace Claims

theorem new_safe : fits.new.isSome := by simp [fits.new]

theorem new_inv : ∀ (me : fits), fits.new = some me → Inv me := by
  intro me _; simp [Inv]

theorem call_safe : ∀ (me : fits) (n room : BitVec 32), Inv me → (fits.call me n room).isSome := by
  intro me n room _; simp only [fits.call]; split <;> simp

/-- Everything owed. -/
theorem owed : fits.Owed := { new_safe, new_inv, call_safe }

end Claims
end fits
