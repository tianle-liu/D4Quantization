import D4.CertificateC1B1Stage4
import D4.CertificateMoments
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D4.CertificateC1B1
open D4.Certificate

open D4.CertificateMoments

theorem exact_identity : mergeAdd (scale 120000 target) (scale (-12000) sym) = remainder := by kernel_rfl

theorem remainder_nonnegative : nonnegative remainder = true := by kernel_rfl

theorem target_formula : sumFast [scale 12000 momentC1,
    scale (-16000) (mul determinantC1 parameterC1),
    scale 21 (power parameterC1 5)] = target := by
  rw [determinant_product_C1, parameter_power_C1]
  kernel_rfl

theorem target_nonnegative (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x target :=
  certificate_from_nonnegative_sym target sym remainder 120000 12000
    (by decide) (by decide) sym_nonnegative exact_identity remainder_nonnegative x hx

end D4.CertificateC1B1
