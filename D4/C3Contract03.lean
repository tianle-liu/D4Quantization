import D4.C3Contract03Merge3_0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c3Contract03 : Poly := C3Contract03Merge3_0
theorem c3Contract03_factors : List.flatten [C3Contract03Factor0,C3Contract03Factor1,C3Contract03Factor2,C3Contract03Factor3,C3Contract03Factor4,C3Contract03Factor5,C3Contract03Factor6,C3Contract03Factor7,C3Contract03Factor8] = C3.adj03 := by kernel_rfl
theorem c3Contract03_eval (x : Nat → ℝ) : eval x c3Contract03 = eval x c3Tensor03 * eval x C3.adj03 := by
  rw [c3Contract03,C3Contract03Merge3_0_eval,c3Contract03_factors]
end D4.Secondary
