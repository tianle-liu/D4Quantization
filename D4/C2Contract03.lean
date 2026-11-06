import D4.C2Contract03Merge2_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c2Contract03 : Poly := C2Contract03Merge2_0
theorem c2Contract03_factors : List.flatten [C2Contract03Factor0,C2Contract03Factor1,C2Contract03Factor2,C2Contract03Factor3,C2Contract03Factor4,C2Contract03Factor5,C2Contract03Factor6,C2Contract03Factor7] = C2.adj03 := by kernel_rfl
theorem c2Contract03_eval (x : Nat → ℝ) : eval x c2Contract03 = eval x c2Tensor03 * eval x C2.adj03 := by
  rw [c2Contract03,C2Contract03Merge2_0_eval,c2Contract03_factors]
end D4.Secondary
