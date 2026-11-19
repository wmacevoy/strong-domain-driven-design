import frame_beginsOwed

/-! The proofs about frame_begins, a function that is not a method. Nothing here is trusted, and
nothing here says what is owed: that is `frame_begins.Owed`, generated from the function as it
stands in its own file, and `owed`, at the end, is a proof of it. -/

namespace frame_begins
namespace Claims

theorem new_safe : frame_begins.new.isSome := by
  simp [frame_begins.new]

theorem new_inv : ∀ (me : frame_begins), frame_begins.new = some me → Inv me := by
  intro me _; simp [Inv]

/-- It reads bytes 0 to 3, and only after it has seen that there are four. -/
theorem call_safe : ∀ (me : frame_begins) (data : Prooc.Bytes), Inv me →
    (frame_begins.call me data).isSome := by
  intro me data _
  have hlen := Prooc.Bytes.size_toNat data
  simp only [frame_begins.call]
  by_cases h : Prooc.Bytes.size data < 4#64
  · simp [h]
  · have h4 : 4 ≤ data.bytes.size := by bv_omega
    simp (disch := omega) [h, Prooc.Bytes.read_of_lt]
    repeat (first | split | simp)

/-- Everything owed. -/
theorem owed : frame_begins.Owed :=
  { new_safe, new_inv, call_safe }

end Claims
end frame_begins
