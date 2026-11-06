import D4.CertificateMomentData
import D4.KernelCompute
import D4.CertificateMomentC2Checks
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D4.CertificateMoments
open D4.Certificate

theorem determinant_product_C3 : mul determinantC3 parameterC3 = determinantProductC3 := by kernel_rfl

theorem parameter_power_C3 : power parameterC3 5 = parameterPowerC3 := parameter_power_C2

theorem base_identity_C3 : mergeAdd momentC3 (scale (-5) determinantProductC3) = baseC3 := by kernel_rfl

theorem base_coefficients_nonnegative_C3 : nonnegative baseC3 = true := by kernel_rfl

theorem base_nonnegative_c3 (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x baseC3 :=
  eval_nonneg x hx baseC3 base_coefficients_nonnegative_C3

end D4.CertificateMoments
