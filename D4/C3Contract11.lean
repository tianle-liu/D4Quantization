import D4.C3Contract11Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c3Contract11 : Poly := C3Contract11Merge3_0
theorem c3Contract11_factors : List.flatten [C3Contract11Factor0,C3Contract11Factor1,C3Contract11Factor2,C3Contract11Factor3,C3Contract11Factor4,C3Contract11Factor5,C3Contract11Factor6,C3Contract11Factor7,C3Contract11Factor8,C3Contract11Factor9,C3Contract11Factor10,C3Contract11Factor11,C3Contract11Factor12,C3Contract11Factor13,C3Contract11Factor14] = C3.adj11 := by kernel_rfl
theorem c3Contract11_eval (x : Nat → ℝ) : eval x c3Contract11 = eval x c3Tensor11 * eval x C3.adj11 := by
  rw [c3Contract11,C3Contract11Merge3_0_eval,c3Contract11_factors]
end D4.Secondary
