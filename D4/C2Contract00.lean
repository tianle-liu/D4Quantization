import D4.C2Contract00Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c2Contract00 : Poly := C2Contract00Merge3_0
theorem c2Contract00_factors : List.flatten [C2Contract00Factor0,C2Contract00Factor1,C2Contract00Factor2,C2Contract00Factor3,C2Contract00Factor4,C2Contract00Factor5,C2Contract00Factor6,C2Contract00Factor7,C2Contract00Factor8,C2Contract00Factor9,C2Contract00Factor10,C2Contract00Factor11,C2Contract00Factor12,C2Contract00Factor13] = C2.adj00 := by kernel_rfl
theorem c2Contract00_eval (x : Nat → ℝ) : eval x c2Contract00 = eval x c2Tensor00 * eval x C2.adj00 := by
  rw [c2Contract00,C2Contract00Merge3_0_eval,c2Contract00_factors]
end D4.Secondary
