import D4.CertificateC2B2Stage2
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D4.CertificateC2B2
open D4.Certificate

theorem symmetryImage3_0_eq : rename [0,1,2,3,4,5,6,7,8,9] symStage2 = symmetryImage3_0 := by kernel_rfl

theorem symmetryImage3_1_eq : rename [0,1,2,4,3,6,5,8,7,9] symStage2 = symmetryImage3_1 := by kernel_rfl

theorem symmetryImage3_2_eq : rename [0,5,7,9,3,6,1,8,2,4] symStage2 = symmetryImage3_2 := by kernel_rfl

theorem expand_symmetry3 : sumFast (representatives3.map fun g => rename g symStage2) = sym := by
  simp only [representatives3, List.map_cons, List.map_nil, symmetryImage3_0_eq, symmetryImage3_1_eq, symmetryImage3_2_eq]
  kernel_rfl

theorem sym_nonnegative (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x sym := by
  rw [← expand_symmetry3]
  exact substitution_sum_nonneg symStage2 representatives3 symStage2_nonnegative x hx

end D4.CertificateC2B2
