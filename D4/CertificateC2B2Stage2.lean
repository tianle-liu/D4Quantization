import D4.CertificateC2B2Stage1
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D4.CertificateC2B2
open D4.Certificate

theorem symmetryImage2_0_eq : rename [0,1,2,3,4,5,6,7,8,9] symStage1 = symmetryImage2_0 := by kernel_rfl

theorem symmetryImage2_1_eq : rename [0,5,7,3,9,1,6,2,8,4] symStage1 = symmetryImage2_1 := by kernel_rfl

theorem expand_symmetry2 : sumFast (representatives2.map fun g => rename g symStage1) = symStage2 := by
  simp only [representatives2, List.map_cons, List.map_nil, symmetryImage2_0_eq, symmetryImage2_1_eq]
  kernel_rfl

theorem symStage2_nonnegative (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x symStage2 := by
  rw [← expand_symmetry2]
  exact substitution_sum_nonneg symStage1 representatives2 symStage1_nonnegative x hx

end D4.CertificateC2B2
