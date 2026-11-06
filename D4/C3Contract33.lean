import D4.C3Contract33Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c3Contract33 : Poly := C3Contract33Merge3_0
theorem c3Contract33_factors : List.flatten [C3Contract33Factor0,C3Contract33Factor1,C3Contract33Factor2,C3Contract33Factor3,C3Contract33Factor4,C3Contract33Factor5,C3Contract33Factor6,C3Contract33Factor7,C3Contract33Factor8,C3Contract33Factor9,C3Contract33Factor10,C3Contract33Factor11,C3Contract33Factor12,C3Contract33Factor13,C3Contract33Factor14] = C3.adj33 := by kernel_rfl
theorem c3Contract33_eval (x : Nat → ℝ) : eval x c3Contract33 = eval x c3Tensor33 * eval x C3.adj33 := by
  rw [c3Contract33,C3Contract33Merge3_0_eval,c3Contract33_factors]
end D4.Secondary
