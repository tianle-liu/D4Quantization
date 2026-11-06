import D4.CertificateC2B1Base
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D4.CertificateC2B1
open D4.Certificate

theorem symmetryImage1_0_eq : rename [0,1,2,3,4,5,6,7,8,9] unsym = symmetryImage1_0 := by kernel_rfl

theorem symmetryImage1_1_eq : rename [0,2,1,3,4,7,8,5,6,9] unsym = symmetryImage1_1 := by kernel_rfl

theorem expand_symmetry1 : sumFast (representatives1.map fun g => rename g unsym) = symStage1 := by
  simp only [representatives1, List.map_cons, List.map_nil, symmetryImage1_0_eq, symmetryImage1_1_eq]
  kernel_rfl

theorem symStage1_nonnegative (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x symStage1 := by
  rw [← expand_symmetry1]
  exact substitution_sum_nonneg unsym representatives1 unsym_nonnegative x hx

end D4.CertificateC2B1
