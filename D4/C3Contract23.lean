import D4.C3Contract23Merge2_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c3Contract23 : Poly := C3Contract23Merge2_0
theorem c3Contract23_factors : List.flatten [C3Contract23Factor0,C3Contract23Factor1,C3Contract23Factor2,C3Contract23Factor3,C3Contract23Factor4,C3Contract23Factor5,C3Contract23Factor6] = C3.adj23 := by kernel_rfl
theorem c3Contract23_eval (x : Nat → ℝ) : eval x c3Contract23 = eval x c3Tensor23 * eval x C3.adj23 := by
  rw [c3Contract23,C3Contract23Merge2_0_eval,c3Contract23_factors]
end D4.Secondary
