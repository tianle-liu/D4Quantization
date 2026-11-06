import D4.AreaSquareEnvelope

/-! Exact integrals, rather than formal antiderivative assertions, of the
quadratic sublevel areas in the two local corrections. -/
noncomputable section
namespace D4.C23Local
open Set MeasureTheory

theorem quadratic_area_convolution (A B C t : ℝ) :
    (∫ s in (0:ℝ)..t, (t-s)^2*(A+B*s+C*s^2)) =
      A*t^3/3+B*t^4/12+C*t^5/30 := by
  have he : (fun s : ℝ => (t-s)^2*(A+B*s+C*s^2)) =
      fun s => A*t^2+(B*t^2-2*A*t)*s+(A-2*B*t+C*t^2)*s^2+
        (B-2*C*t)*s^3+C*s^4 := by funext s; ring
  rw [he]
  have h₀ : IntervalIntegrable (fun _ : ℝ => A*t^2) volume 0 t := intervalIntegrable_const
  have h₁ : IntervalIntegrable (fun s : ℝ => (B*t^2-2*A*t)*s) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun s : ℝ => (A-2*B*t+C*t^2)*s^2) volume 0 t :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  have h₃ : IntervalIntegrable (fun s : ℝ => (B-2*C*t)*s^3) volume 0 t :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable _ _
  have h₄ : IntervalIntegrable (fun s : ℝ => C*s^4) volume 0 t :=
    (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (((h₀.add h₁).add h₂).add h₃) h₄,
    intervalIntegral.integral_add ((h₀.add h₁).add h₂) h₃,
    intervalIntegral.integral_add (h₀.add h₁) h₂,
    intervalIntegral.integral_add h₀ h₁,intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    integral_id,integral_pow,integral_pow,integral_pow]
  simp only [smul_eq_mul]
  norm_num
  ring

theorem correction2_integral (a p q r : ℝ) (ha : 0 ≤ a) :
    (15/8:ℝ)*(∫ s in Icc 0 (2*a), (2*a-s)^2*
      (4*(p*q+p*r+q*r)+4*(p+q+r)*s+2*s^2)) =
      2*a^3*(2*a^2+5*a*(p+q+r)+10*(p*q+p*r+q*r)) := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le
    (by linarith : (0:ℝ) ≤ 2*a),quadratic_area_convolution]
  ring

theorem correction3_integral (b u v : ℝ) (hb : 0 ≤ b) :
    (15/8:ℝ)*(∫ s in Icc 0 (2*b), (2*b-s)^2*
      ((2*u-2*b)*(2*v-2*b)+2*((2*u-2*b)+(2*v-2*b))*s+3*s^2)) =
      2*b^3*(3*b^2-5*b*(u+v)+10*u*v) := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le
    (by linarith : (0:ℝ) ≤ 2*b),quadratic_area_convolution]
  ring

end D4.C23Local
