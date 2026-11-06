import D4.CertificateMomentData
import D4.KernelCompute
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D4.CertificateMoments
open D4.Certificate

theorem determinant_product_C1 : mul determinantC1 parameterC1 = determinantProductC1 := by kernel_rfl

theorem parameter_power_step1_C1 : mul [([],1)] parameterC1 = parameterC1 := by kernel_rfl

theorem parameter_power_step2_C1 : mul parameterC1 parameterC1 = parameterPower2C1 := by kernel_rfl

theorem parameter_power_step3_C1 : mul parameterPower2C1 parameterC1 = parameterPower3C1 := by kernel_rfl

theorem parameter_power_step4_C1 : mul parameterPower3C1 parameterC1 = parameterPower4C1 := by kernel_rfl

theorem parameter_power_step5_C1 : mul parameterPower4C1 parameterC1 = parameterPowerC1 := by kernel_rfl

theorem parameter_power_C1 : power parameterC1 5 = parameterPowerC1 := by
  simp only [power, parameter_power_step1_C1, parameter_power_step2_C1, parameter_power_step3_C1, parameter_power_step4_C1, parameter_power_step5_C1]

theorem base_identity_C1 : mergeAdd momentC1 (scale (-1) determinantProductC1) = baseC1 := by kernel_rfl

theorem base_coefficients_nonnegative_C1 : nonnegative baseC1 = true := by kernel_rfl

theorem base_nonnegative_c1 (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x baseC1 :=
  eval_nonneg x hx baseC1 base_coefficients_nonnegative_C1

end D4.CertificateMoments
