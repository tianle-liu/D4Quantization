import D4.C3Contract13Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c3Contract13 : Poly := C3Contract13Merge3_0
theorem c3Contract13_factors : List.flatten [C3Contract13Factor0,C3Contract13Factor1,C3Contract13Factor2,C3Contract13Factor3,C3Contract13Factor4,C3Contract13Factor5,C3Contract13Factor6,C3Contract13Factor7,C3Contract13Factor8] = C3.adj13 := by kernel_rfl
theorem c3Contract13_eval (x : Nat → ℝ) : eval x c3Contract13 = eval x c3Tensor13 * eval x C3.adj13 := by
  rw [c3Contract13,C3Contract13Merge3_0_eval,c3Contract13_factors]
end D4.Secondary
