import D4.C3Contract01Merge2_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c3Contract01 : Poly := C3Contract01Merge2_0
theorem c3Contract01_factors : List.flatten [C3Contract01Factor0,C3Contract01Factor1,C3Contract01Factor2,C3Contract01Factor3,C3Contract01Factor4,C3Contract01Factor5] = C3.adj01 := by kernel_rfl
theorem c3Contract01_eval (x : Nat → ℝ) : eval x c3Contract01 = eval x c3Tensor01 * eval x C3.adj01 := by
  rw [c3Contract01,C3Contract01Merge2_0_eval,c3Contract01_factors]
end D4.Secondary
