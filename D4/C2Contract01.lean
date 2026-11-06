import D4.C2Contract01Merge2_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c2Contract01 : Poly := C2Contract01Merge2_0
theorem c2Contract01_factors : List.flatten [C2Contract01Factor0,C2Contract01Factor1,C2Contract01Factor2,C2Contract01Factor3,C2Contract01Factor4,C2Contract01Factor5] = C2.adj01 := by kernel_rfl
theorem c2Contract01_eval (x : Nat → ℝ) : eval x c2Contract01 = eval x c2Tensor01 * eval x C2.adj01 := by
  rw [c2Contract01,C2Contract01Merge2_0_eval,c2Contract01_factors]
end D4.Secondary
