import D4.CertificateC3B2Stage3
import D4.CertificateMoments
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D4.CertificateC3B2
open D4.Certificate

open D4.CertificateMoments

theorem exact_identity : mergeAdd (scale 3600000 target) (scale (-256) sym) = remainder := by kernel_rfl

theorem remainder_nonnegative : nonnegative remainder = true := by kernel_rfl

theorem target_formula : sumFast [scale 256 momentC3,
    scale (-1984) (mul determinantC3 parameterC3),
    scale 5 (power parameterC3 5)] = target := by
  rw [determinant_product_C3, parameter_power_C3]
  kernel_rfl

theorem target_nonnegative (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x target :=
  certificate_from_nonnegative_sym target sym remainder 3600000 256
    (by decide) (by decide) sym_nonnegative exact_identity remainder_nonnegative x hx

end D4.CertificateC3B2
