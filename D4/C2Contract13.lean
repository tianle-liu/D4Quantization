import D4.C2Contract13Merge2_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c2Contract13 : Poly := C2Contract13Merge2_0
theorem c2Contract13_factors : List.flatten [C2Contract13Factor0,C2Contract13Factor1,C2Contract13Factor2,C2Contract13Factor3,C2Contract13Factor4,C2Contract13Factor5,C2Contract13Factor6,C2Contract13Factor7] = C2.adj13 := by kernel_rfl
theorem c2Contract13_eval (x : Nat → ℝ) : eval x c2Contract13 = eval x c2Tensor13 * eval x C2.adj13 := by
  rw [c2Contract13,C2Contract13Merge2_0_eval,c2Contract13_factors]
end D4.Secondary
