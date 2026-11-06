import D4.PrincipalTreeContract22Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Principal
open Certificate
def contract22 : Poly := contract22Merge3_0
theorem contract22_factors : List.flatten [contract22Factor0,contract22Factor1,contract22Factor2,contract22Factor3,contract22Factor4,contract22Factor5,contract22Factor6,contract22Factor7,contract22Factor8,contract22Factor9] = adj22 := by kernel_rfl
theorem contract22_eval (x : Nat → ℝ) : eval x contract22 = eval x tensor22 * eval x adj22 := by
  rw [contract22,contract22Merge3_0_eval,contract22_factors]
end D4.Principal
