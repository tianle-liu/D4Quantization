import D4.C3Contract22Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c3Contract22 : Poly := C3Contract22Merge3_0
theorem c3Contract22_factors : List.flatten [C3Contract22Factor0,C3Contract22Factor1,C3Contract22Factor2,C3Contract22Factor3,C3Contract22Factor4,C3Contract22Factor5,C3Contract22Factor6,C3Contract22Factor7,C3Contract22Factor8,C3Contract22Factor9,C3Contract22Factor10,C3Contract22Factor11,C3Contract22Factor12,C3Contract22Factor13,C3Contract22Factor14] = C3.adj22 := by kernel_rfl
theorem c3Contract22_eval (x : Nat → ℝ) : eval x c3Contract22 = eval x c3Tensor22 * eval x C3.adj22 := by
  rw [c3Contract22,C3Contract22Merge3_0_eval,c3Contract22_factors]
end D4.Secondary
