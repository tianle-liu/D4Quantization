import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Actual polar integration in a finite-dimensional normed space. The
spherical measure is Mathlib's Haar-induced measure, not a postulated
surface measure or an additional integration axiom. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory MeasureTheory.Measure

theorem integral_polar_product {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) :
    (∫ x, f x ∂μ) =
      ∫ p : sphere (0:E) 1 × Ioi (0:ℝ), f (p.2.1 • p.1.1)
        ∂(μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1))) := by
  calc
    (∫ x, f x ∂μ) = ∫ x : ({(0:E)}ᶜ : Set E), f x.1 ∂(μ.comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f,
        restrict_compl_singleton]
    _ = _ := by
      have H := μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _) (fun p : sphere (0:E) 1 × Ioi (0:ℝ) =>
          f (p.2.1 • p.1.1))
      simpa only [← homeomorphUnitSphereProd_symm_apply_coe,
        Homeomorph.symm_apply_apply] using H

theorem integral_ball_radial {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (R : ℝ) (f : ℝ → ℝ) :
    (∫ x in ball (0:E) R, f ‖x‖ ∂μ) =
      (Module.finrank ℝ E : ℝ) * μ.real (ball (0:E) 1) *
        ∫ r in Ioo (0:ℝ) R, r^(Module.finrank ℝ E-1)*f r := by
  have he : (fun x : E => (ball (0:E) R).indicator (fun x => f ‖x‖) x) =
      fun x => (Iio R).indicator f ‖x‖ := by
    funext x
    simp only [indicator, mem_ball_zero_iff, mem_Iio]
  rw [← integral_indicator measurableSet_ball, he,
    integral_fun_norm_addHaar μ ((Iio R).indicator f)]
  simp only [nsmul_eq_mul, smul_eq_mul]
  have hi : (fun r : ℝ => r^(Module.finrank ℝ E-1)*(Iio R).indicator f r) =
      (Iio R).indicator (fun r => r^(Module.finrank ℝ E-1)*f r) := by
    funext r
    by_cases hr : r < R <;> simp [Set.indicator, hr]
  rw [hi, setIntegral_indicator measurableSet_Iio]
  exact (mul_assoc _ _ _).symm

/-- Integration of any nonnegative integer radial moment over an actual
ball, in terms of the actual volume of the unit ball. -/
theorem integral_norm_pow_ball {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (∫ x in ball (0:E) R, ‖x‖^p ∂μ) =
      (Module.finrank ℝ E : ℝ) * μ.real (ball (0:E) 1) *
        R^(Module.finrank ℝ E+p) / (Module.finrank ℝ E+p) := by
  let n := Module.finrank ℝ E
  have hn : 0 < n := Module.finrank_pos
  have he : (fun x : E => (ball (0:E) R).indicator (fun x => ‖x‖^p) x) =
      fun x => (Iio R).indicator (fun t : ℝ => t^p) ‖x‖ := by
    funext x
    simp only [indicator, mem_ball_zero_iff, mem_Iio]
  rw [← integral_indicator measurableSet_ball, he,
    integral_fun_norm_addHaar μ ((Iio R).indicator (fun t : ℝ => t^p))]
  simp only [nsmul_eq_mul, smul_eq_mul]
  have hi : (∫ r in Ioi (0:ℝ), r^(n-1) * (Iio R).indicator (fun t : ℝ => t^p) r) =
      ∫ r in Ioo (0:ℝ) R, r^(n-1+p) := by
    have he' : (fun r : ℝ => r^(n-1) * (Iio R).indicator (fun t : ℝ => t^p) r) =
        (Iio R).indicator (fun r => r^(n-1+p)) := by
      funext r
      by_cases hr : r < R <;> simp [Set.indicator, hr, pow_add]
    rw [he', setIntegral_indicator measurableSet_Iio]
    rfl
  rw [hi, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hR, integral_pow]
  have hn' : n-1+p+1 = n+p := by omega
  rw [hn']
  simp only [Nat.cast_add, zero_pow (by omega : n+p ≠ 0), sub_zero]
  simp only [Nat.cast_sub hn, Nat.cast_one]
  change (n:ℝ) * (μ.real (ball (0:E) 1) * (R^(n+p)/((n:ℝ)-1+(p:ℝ)+1))) = _
  ring

end D4.ConeAnalysis
