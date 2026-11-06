import D4.PrincipalTreeContract00Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Principal
open Certificate
def contract00 : Poly := contract00Merge3_0
theorem contract00_factors : List.flatten [contract00Factor0,contract00Factor1,contract00Factor2,contract00Factor3,contract00Factor4,contract00Factor5,contract00Factor6,contract00Factor7,contract00Factor8,contract00Factor9] = adj00 := by kernel_rfl
theorem contract00_eval (x : Nat → ℝ) : eval x contract00 = eval x tensor00 * eval x adj00 := by
  rw [contract00,contract00Merge3_0_eval,contract00_factors]
end D4.Principal
