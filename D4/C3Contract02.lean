import D4.C3Contract02Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c3Contract02 : Poly := C3Contract02Merge3_0
theorem c3Contract02_factors : List.flatten [C3Contract02Factor0,C3Contract02Factor1,C3Contract02Factor2,C3Contract02Factor3,C3Contract02Factor4,C3Contract02Factor5,C3Contract02Factor6,C3Contract02Factor7,C3Contract02Factor8] = C3.adj02 := by kernel_rfl
theorem c3Contract02_eval (x : Nat → ℝ) : eval x c3Contract02 = eval x c3Tensor02 * eval x C3.adj02 := by
  rw [c3Contract02,C3Contract02Merge3_0_eval,c3Contract02_factors]
end D4.Secondary
