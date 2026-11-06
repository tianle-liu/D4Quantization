import D4.CertificateC3B2Stage2
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D4.CertificateC3B2
open D4.Certificate

theorem symmetryImage3_0_eq : rename [0,1,2,3,4,5,6,7,8,9] symStage2 = symmetryImage3_0 := by kernel_rfl

theorem symmetryImage3_1_eq : rename [0,2,1,3,4,7,8,5,6,9] symStage2 = symmetryImage3_1 := by kernel_rfl

theorem symmetryImage3_2_eq : rename [0,3,6,1,7,5,2,4,9,8] symStage2 = symmetryImage3_2 := by kernel_rfl

theorem symmetryImage3_3_eq : rename [0,4,5,1,8,6,2,3,9,7] symStage2 = symmetryImage3_3 := by kernel_rfl

theorem symmetryImage3_4_eq : rename [0,5,4,1,8,3,9,6,2,7] symStage2 = symmetryImage3_4 := by kernel_rfl

theorem symmetryImage3_5_eq : rename [0,6,3,1,7,4,9,5,2,8] symStage2 = symmetryImage3_5 := by kernel_rfl

theorem symmetryImage3_6_eq : rename [0,7,4,2,6,3,9,8,1,5] symStage2 = symmetryImage3_6 := by kernel_rfl

theorem symmetryImage3_7_eq : rename [0,8,3,2,5,4,9,7,1,6] symStage2 = symmetryImage3_7 := by kernel_rfl

theorem symmetryImage3_8_eq : rename [0,9,1,5,6,8,7,3,4,2] symStage2 = symmetryImage3_8 := by kernel_rfl

theorem expand_symmetry3 : sumFast (representatives3.map fun g => rename g symStage2) = sym := by
  simp only [representatives3, List.map_cons, List.map_nil, symmetryImage3_0_eq, symmetryImage3_1_eq, symmetryImage3_2_eq, symmetryImage3_3_eq, symmetryImage3_4_eq, symmetryImage3_5_eq, symmetryImage3_6_eq, symmetryImage3_7_eq, symmetryImage3_8_eq]
  kernel_rfl

theorem sym_nonnegative (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x sym := by
  rw [← expand_symmetry3]
  exact substitution_sum_nonneg symStage2 representatives3 symStage2_nonnegative x hx

end D4.CertificateC3B2
