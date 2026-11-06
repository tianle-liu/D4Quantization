import D4.CertificateMomentData
import D4.KernelCompute
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D4.CertificateMoments
open D4.Certificate

theorem determinant_product_C2 : mul determinantC2 parameterC2 = determinantProductC2 := by kernel_rfl

theorem parameter_power_step1_C2 : mul [([],1)] parameterC2 = parameterC2 := by kernel_rfl

theorem parameter_power_step2_C2 : mul parameterC2 parameterC2 = parameterPower2C2 := by kernel_rfl

theorem parameter_power_step3_C2 : mul parameterPower2C2 parameterC2 = parameterPower3C2 := by kernel_rfl

theorem parameter_power_step4_C2 : mul parameterPower3C2 parameterC2 = parameterPower4C2 := by kernel_rfl

theorem parameter_power_step5_C2 : mul parameterPower4C2 parameterC2 = parameterPowerC2 := by kernel_rfl

theorem parameter_power_C2 : power parameterC2 5 = parameterPowerC2 := by
  simp only [power, parameter_power_step1_C2, parameter_power_step2_C2, parameter_power_step3_C2, parameter_power_step4_C2, parameter_power_step5_C2]

theorem base_identity_C2 : mergeAdd momentC2 (scale (-5) determinantProductC2) = baseC2 := by kernel_rfl

theorem base_coefficients_nonnegative_C2 : nonnegative baseC2 = true := by kernel_rfl

theorem base_nonnegative_c2 (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x baseC2 :=
  eval_nonneg x hx baseC2 base_coefficients_nonnegative_C2

end D4.CertificateMoments
