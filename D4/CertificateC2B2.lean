import D4.CertificateC2B2Stage3
import D4.CertificateMoments
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D4.CertificateC2B2
open D4.Certificate

open D4.CertificateMoments

theorem exact_identity : mergeAdd (scale 120000 target) (scale (-256) sym) = remainder := by kernel_rfl

theorem remainder_nonnegative : nonnegative remainder = true := by kernel_rfl

theorem target_formula : sumFast [scale 256 momentC2,
    scale (-1984) (mul determinantC2 parameterC2),
    scale 5 (power parameterC2 5)] = target := by
  rw [determinant_product_C2, parameter_power_C2]
  kernel_rfl

theorem target_nonnegative (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x target :=
  certificate_from_nonnegative_sym target sym remainder 120000 256
    (by decide) (by decide) sym_nonnegative exact_identity remainder_nonnegative x hx

end D4.CertificateC2B2
