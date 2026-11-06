import D4.C2Contract33Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c2Contract33 : Poly := C2Contract33Merge3_0
theorem c2Contract33_factors : List.flatten [C2Contract33Factor0,C2Contract33Factor1,C2Contract33Factor2,C2Contract33Factor3,C2Contract33Factor4,C2Contract33Factor5,C2Contract33Factor6,C2Contract33Factor7,C2Contract33Factor8,C2Contract33Factor9,C2Contract33Factor10,C2Contract33Factor11,C2Contract33Factor12] = C2.adj33 := by kernel_rfl
theorem c2Contract33_eval (x : Nat → ℝ) : eval x c2Contract33 = eval x c2Tensor33 * eval x C2.adj33 := by
  rw [c2Contract33,C2Contract33Merge3_0_eval,c2Contract33_factors]
end D4.Secondary
