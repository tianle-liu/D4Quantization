import D4.C2Contract12Merge2_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c2Contract12 : Poly := C2Contract12Merge2_0
theorem c2Contract12_factors : List.flatten [C2Contract12Factor0,C2Contract12Factor1,C2Contract12Factor2,C2Contract12Factor3,C2Contract12Factor4,C2Contract12Factor5,C2Contract12Factor6,C2Contract12Factor7] = C2.adj12 := by kernel_rfl
theorem c2Contract12_eval (x : Nat → ℝ) : eval x c2Contract12 = eval x c2Tensor12 * eval x C2.adj12 := by
  rw [c2Contract12,C2Contract12Merge2_0_eval,c2Contract12_factors]
end D4.Secondary
