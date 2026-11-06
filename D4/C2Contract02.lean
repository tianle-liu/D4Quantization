import D4.C2Contract02Merge2_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c2Contract02 : Poly := C2Contract02Merge2_0
theorem c2Contract02_factors : List.flatten [C2Contract02Factor0,C2Contract02Factor1,C2Contract02Factor2,C2Contract02Factor3,C2Contract02Factor4,C2Contract02Factor5,C2Contract02Factor6,C2Contract02Factor7] = C2.adj02 := by kernel_rfl
theorem c2Contract02_eval (x : Nat → ℝ) : eval x c2Contract02 = eval x c2Tensor02 * eval x C2.adj02 := by
  rw [c2Contract02,C2Contract02Merge2_0_eval,c2Contract02_factors]
end D4.Secondary
