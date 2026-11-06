import D4.PrincipalTreeContractionMerge3_0
import D4.CertificateSumTen
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Principal
open Certificate
def contractionPolys : List Poly := [contract00,(scale 2 contract01),(scale 2 contract02),(scale 2 contract03),contract11,(scale 2 contract12),(scale 2 contract13),contract22,(scale 2 contract23),contract33]
theorem contraction_check : sumFast contractionPolys = treeMomentProduct := by
  simp (config := {implicitDefEqProofs := false}) only [contractionPolys,sumFast_ten,
    principalTreeContractionMerge0_0_check,
    principalTreeContractionMerge0_1_check,
    principalTreeContractionMerge0_2_check,
    principalTreeContractionMerge0_3_check,
    principalTreeContractionMerge0_4_check,
    principalTreeContractionMerge1_0_check,
    principalTreeContractionMerge1_1_check,
    principalTreeContractionMerge2_0_check,
    principalTreeContractionMerge3_0_check]
end D4.Principal
