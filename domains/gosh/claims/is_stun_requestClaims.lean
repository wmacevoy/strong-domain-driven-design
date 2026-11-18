import is_stun_requestOwed

/-! The proofs about is_stun_request, gosh's function (src/meetup/answer.h), which a meetup asks of
every datagram anyone sends it. Nothing here is trusted, and nothing here says what is owed: that
is `is_stun_request.Owed`, generated from the function as it stands, and `owed`, at the end, is a
proof of it. -/

namespace is_stun_request
namespace Claims

theorem new_safe : is_stun_request.new.isSome := by
  simp [is_stun_request.new]

theorem new_inv : ∀ (me : is_stun_request), is_stun_request.new = some me → Inv me := by
  intro me _; simp [Inv]

/-- It reads bytes 0 to 7, and only where it has seen that there are at least 20: C++ does not
look at the right side of `||` when the left is true. -/
theorem call_safe : ∀ (me : is_stun_request) (request : Prooc.Bytes), Inv me →
    (is_stun_request.call me request).isSome := by
  intro me request _
  have hlen := Prooc.Bytes.size_toNat request
  simp only [is_stun_request.call]
  by_cases h : Prooc.Bytes.size request < 20#64 ∨ Prooc.Bytes.size request > 200#64
  · simp [h]
  · have h20 : 20 ≤ request.bytes.size := by bv_omega
    simp (disch := omega) [h, Prooc.Bytes.read_of_lt]
    repeat (first | split | simp)

/-- Everything owed. -/
theorem owed : is_stun_request.Owed :=
  { new_safe, new_inv, call_safe }

end Claims
end is_stun_request
