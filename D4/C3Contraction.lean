import D4.C3ContractionMerge3_0
import D4.CertificateSumTen
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c3ContractionPolys : List Poly := [c3Contract00,(scale 2 c3Contract01),(scale 2 c3Contract02),(scale 2 c3Contract03),c3Contract11,(scale 2 c3Contract12),(scale 2 c3Contract13),c3Contract22,(scale 2 c3Contract23),c3Contract33]
theorem c3_contraction_check : sumFast c3ContractionPolys = scale 768 c3MomentProduct := by
  simp (config := {implicitDefEqProofs := false}) only [c3ContractionPolys,sumFast_ten,
    c3ContractionMerge0_0_check,
    c3ContractionMerge0_1_check,
    c3ContractionMerge0_2_check,
    c3ContractionMerge0_3_check,
    c3ContractionMerge0_4_check,
    c3ContractionMerge1_0_check,
    c3ContractionMerge1_1_check,
    c3ContractionMerge2_0_check,
    c3ContractionMerge3_0_check]
end D4.Secondary
