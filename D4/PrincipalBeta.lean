import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Polynomial beta integrals used by simplex slicing. -/
noncomputable section
open MeasureTheory Set
namespace D4.Principal

theorem betaIntegral_nat (m n : ℕ) :
    Complex.betaIntegral ((m : ℂ) + 1) ((n : ℂ) + 1) =
      (m.factorial : ℂ) * n.factorial / (m + n + 1).factorial := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (m : ℂ) + 1) (t := (n : ℂ) + 1) (by simp; positivity) (by simp; positivity)
  have he : (m : ℂ) + 1 + ((n : ℂ) + 1) = ((m + n + 1 : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  rw [he, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial] at h
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero (m + n + 1))).mpr
  simpa only [mul_comm] using h.symm

theorem integral_pow_mul_sub_pow (m n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ t in Icc 0 r, t ^ m * (r - t) ^ n) =
      (m.factorial : ℝ) * n.factorial / (m + n + 1).factorial * r ^ (m + n + 1) := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    simp
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.le]
  have h := Complex.betaIntegral_scaled ((m : ℂ) + 1) ((n : ℂ) + 1) hr
  have he : (m : ℂ) + 1 + ((n : ℂ) + 1) - 1 = ((m + n + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  simp only [add_sub_cancel_right, he, Complex.cpow_natCast, betaIntegral_nat] at h
  have hc : (∫ t in (0 : ℝ)..r, (t : ℂ) ^ m * ((r : ℂ) - t) ^ n) =
      ((∫ t in (0 : ℝ)..r, t ^ m * (r - t) ^ n) : ℝ) := by
    norm_cast
    exact intervalIntegral.integral_ofReal
  rw [hc] at h
  apply Complex.ofReal_injective
  push_cast
  simpa only [mul_comm] using h

end D4.Principal
