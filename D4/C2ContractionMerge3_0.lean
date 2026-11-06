import D4.CertificatePrimitiveScale
import D4.C2ContractionMerge2_0
import D4.C2ContractionMerge0_4
import D4.C2MomentProduct
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
theorem c2ContractionMerge3_0_check : mergeAdd c2ContractionMerge2_0 c2ContractionMerge0_4 = scale 768 c2MomentProduct := by
  rw [← scalePrim_eq_scale]
  kernel_rfl
end D4.Secondary
