import D4.PaperSymmetryAction
import D4.PaperSymmetryC3
import D4.CertificateC3B1Data
import D4.CertificateC3B2Data
import D4.KernelCompute
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.PaperSymmetry.C3
/-- The actual generated subgroup is exactly the permutation list used by both certificates. -/
theorem certificate_group_b1 : elements.map encoding=D4.CertificateC3B1.group := by kernel_rfl
theorem certificate_group_b2 : elements.map encoding=D4.CertificateC3B2.group := by kernel_rfl
end D4.PaperSymmetry.C3
