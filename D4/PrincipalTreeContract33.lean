import D4.PrincipalTreeContract33Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Principal
open Certificate
def contract33 : Poly := contract33Merge3_0
theorem contract33_factors : List.flatten [contract33Factor0,contract33Factor1,contract33Factor2,contract33Factor3,contract33Factor4,contract33Factor5,contract33Factor6,contract33Factor7,contract33Factor8,contract33Factor9] = adj33 := by kernel_rfl
theorem contract33_eval (x : Nat → ℝ) : eval x contract33 = eval x tensor33 * eval x adj33 := by
  rw [contract33,contract33Merge3_0_eval,contract33_factors]
end D4.Principal
