import D4.C2Contract11Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c2Contract11 : Poly := C2Contract11Merge3_0
theorem c2Contract11_factors : List.flatten [C2Contract11Factor0,C2Contract11Factor1,C2Contract11Factor2,C2Contract11Factor3,C2Contract11Factor4,C2Contract11Factor5,C2Contract11Factor6,C2Contract11Factor7,C2Contract11Factor8,C2Contract11Factor9,C2Contract11Factor10,C2Contract11Factor11,C2Contract11Factor12,C2Contract11Factor13] = C2.adj11 := by kernel_rfl
theorem c2Contract11_eval (x : Nat → ℝ) : eval x c2Contract11 = eval x c2Tensor11 * eval x C2.adj11 := by
  rw [c2Contract11,C2Contract11Merge3_0_eval,c2Contract11_factors]
end D4.Secondary
