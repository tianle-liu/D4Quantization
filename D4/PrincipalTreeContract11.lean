import D4.PrincipalTreeContract11Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Principal
open Certificate
def contract11 : Poly := contract11Merge3_0
theorem contract11_factors : List.flatten [contract11Factor0,contract11Factor1,contract11Factor2,contract11Factor3,contract11Factor4,contract11Factor5,contract11Factor6,contract11Factor7,contract11Factor8,contract11Factor9] = adj11 := by kernel_rfl
theorem contract11_eval (x : Nat → ℝ) : eval x contract11 = eval x tensor11 * eval x adj11 := by
  rw [contract11,contract11Merge3_0_eval,contract11_factors]
end D4.Principal
