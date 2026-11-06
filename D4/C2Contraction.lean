import D4.C2ContractionMerge3_0
import D4.CertificateSumTen
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
def c2ContractionPolys : List Poly := [c2Contract00,(scale 2 c2Contract01),(scale 2 c2Contract02),(scale 2 c2Contract03),c2Contract11,(scale 2 c2Contract12),(scale 2 c2Contract13),c2Contract22,(scale 2 c2Contract23),c2Contract33]
theorem c2_contraction_check : sumFast c2ContractionPolys = scale 768 c2MomentProduct := by
  simp (config := {implicitDefEqProofs := false}) only [c2ContractionPolys,sumFast_ten,
    c2ContractionMerge0_0_check,
    c2ContractionMerge0_1_check,
    c2ContractionMerge0_2_check,
    c2ContractionMerge0_3_check,
    c2ContractionMerge0_4_check,
    c2ContractionMerge1_0_check,
    c2ContractionMerge1_1_check,
    c2ContractionMerge2_0_check,
    c2ContractionMerge3_0_check]
end D4.Secondary
