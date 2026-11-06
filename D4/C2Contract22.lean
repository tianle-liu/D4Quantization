import D4.C2Contract22Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c2Contract22 : Poly := C2Contract22Merge3_0
theorem c2Contract22_factors : List.flatten [C2Contract22Factor0,C2Contract22Factor1,C2Contract22Factor2,C2Contract22Factor3,C2Contract22Factor4,C2Contract22Factor5,C2Contract22Factor6,C2Contract22Factor7,C2Contract22Factor8,C2Contract22Factor9,C2Contract22Factor10,C2Contract22Factor11,C2Contract22Factor12] = C2.adj22 := by kernel_rfl
theorem c2Contract22_eval (x : Nat → ℝ) : eval x c2Contract22 = eval x c2Tensor22 * eval x C2.adj22 := by
  rw [c2Contract22,C2Contract22Merge3_0_eval,c2Contract22_factors]
end D4.Secondary
