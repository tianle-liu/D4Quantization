import D4.C3Contract00Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c3Contract00 : Poly := C3Contract00Merge3_0
theorem c3Contract00_factors : List.flatten [C3Contract00Factor0,C3Contract00Factor1,C3Contract00Factor2,C3Contract00Factor3,C3Contract00Factor4,C3Contract00Factor5,C3Contract00Factor6,C3Contract00Factor7,C3Contract00Factor8,C3Contract00Factor9,C3Contract00Factor10,C3Contract00Factor11,C3Contract00Factor12,C3Contract00Factor13,C3Contract00Factor14] = C3.adj00 := by kernel_rfl
theorem c3Contract00_eval (x : Nat → ℝ) : eval x c3Contract00 = eval x c3Tensor00 * eval x C3.adj00 := by
  rw [c3Contract00,C3Contract00Merge3_0_eval,c3Contract00_factors]
end D4.Secondary
