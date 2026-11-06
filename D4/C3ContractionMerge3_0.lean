import D4.CertificatePrimitiveScale
import D4.C3ContractionMerge2_0
import D4.C3ContractionMerge0_4
import D4.C3MomentProduct
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Certificate
theorem c3ContractionMerge3_0_check : mergeAdd c3ContractionMerge2_0 c3ContractionMerge0_4 = scale 768 c3MomentProduct := by
  rw [← scalePrim_eq_scale]
  kernel_rfl
end D4.Secondary
