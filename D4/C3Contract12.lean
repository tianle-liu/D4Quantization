import D4.C3Contract12Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c3Contract12 : Poly := C3Contract12Merge3_0
theorem c3Contract12_factors : List.flatten [C3Contract12Factor0,C3Contract12Factor1,C3Contract12Factor2,C3Contract12Factor3,C3Contract12Factor4,C3Contract12Factor5,C3Contract12Factor6,C3Contract12Factor7,C3Contract12Factor8] = C3.adj12 := by kernel_rfl
theorem c3Contract12_eval (x : Nat → ℝ) : eval x c3Contract12 = eval x c3Tensor12 * eval x C3.adj12 := by
  rw [c3Contract12,C3Contract12Merge3_0_eval,c3Contract12_factors]
end D4.Secondary
