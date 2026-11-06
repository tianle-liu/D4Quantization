import D4.C2Contract23Merge2_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c2Contract23 : Poly := C2Contract23Merge2_0
theorem c2Contract23_factors : List.flatten [C2Contract23Factor0,C2Contract23Factor1,C2Contract23Factor2,C2Contract23Factor3,C2Contract23Factor4,C2Contract23Factor5,C2Contract23Factor6,C2Contract23Factor7] = C2.adj23 := by kernel_rfl
theorem c2Contract23_eval (x : Nat → ℝ) : eval x c2Contract23 = eval x c2Tensor23 * eval x C2.adj23 := by
  rw [c2Contract23,C2Contract23Merge2_0_eval,c2Contract23_factors]
end D4.Secondary
