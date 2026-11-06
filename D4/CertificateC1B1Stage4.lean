import D4.CertificateC1B1Stage3
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D4.CertificateC1B1
open D4.Certificate

theorem symmetryImage4_0_eq : rename [0,1,2,3,4,5,6,7,8,9] symStage3 = symmetryImage4_0 := by kernel_rfl

theorem symmetryImage4_1_eq : rename [1,0,2,3,4,7,8,5,6,9] symStage3 = symmetryImage4_1 := by kernel_rfl

theorem symmetryImage4_2_eq : rename [2,0,1,3,5,7,9,4,6,8] symStage3 = symmetryImage4_2 := by kernel_rfl

theorem symmetryImage4_3_eq : rename [3,0,1,2,6,8,9,4,5,7] symStage3 = symmetryImage4_3 := by kernel_rfl

theorem symmetryImage4_4_eq : rename [4,0,5,6,1,7,8,2,3,9] symStage3 = symmetryImage4_4 := by kernel_rfl

theorem symmetryImage4_5_eq : rename [5,0,4,6,2,7,9,1,3,8] symStage3 = symmetryImage4_5 := by kernel_rfl

theorem symmetryImage4_6_eq : rename [6,0,4,5,3,8,9,1,2,7] symStage3 = symmetryImage4_6 := by kernel_rfl

theorem symmetryImage4_7_eq : rename [7,1,4,8,2,5,9,0,3,6] symStage3 = symmetryImage4_7 := by kernel_rfl

theorem symmetryImage4_8_eq : rename [8,1,4,7,3,6,9,0,2,5] symStage3 = symmetryImage4_8 := by kernel_rfl

theorem symmetryImage4_9_eq : rename [9,2,5,7,3,6,8,0,1,4] symStage3 = symmetryImage4_9 := by kernel_rfl

theorem expand_symmetry4 : sumFast (representatives4.map fun g => rename g symStage3) = sym := by
  simp only [representatives4, List.map_cons, List.map_nil, symmetryImage4_0_eq, symmetryImage4_1_eq, symmetryImage4_2_eq, symmetryImage4_3_eq, symmetryImage4_4_eq, symmetryImage4_5_eq, symmetryImage4_6_eq, symmetryImage4_7_eq, symmetryImage4_8_eq, symmetryImage4_9_eq]
  kernel_rfl

theorem sym_nonnegative (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x sym := by
  rw [← expand_symmetry4]
  exact substitution_sum_nonneg symStage3 representatives4 symStage3_nonnegative x hx

end D4.CertificateC1B1
