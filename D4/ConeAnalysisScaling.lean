import D4.ConePerspective
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Actual Haar volume and moment scaling, and the matching invariance
of the cone moment perspective. -/
noncomputable section
namespace D4.ConeAnalysis
open Set MeasureTheory MeasureTheory.Measure ConePerspective
open scoped Pointwise

theorem real_measure_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Set E) (c : ℝ) (hc : 0 ≤ c) :
    μ.real (c • S) = c^(Module.finrank ℝ E)*μ.real S := by
  simp only [measureReal_def, addHaar_smul_of_nonneg μ hc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hc _)]

theorem secondMoment_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Set E) (c : ℝ) (hc : 0 < c) :
    (∫ x in c • S, ‖x‖^2 ∂μ) =
      c^(Module.finrank ℝ E+2)*(∫ x in S, ‖x‖^2 ∂μ) := by
  have H := setIntegral_comp_smul_of_pos μ (fun x : E => ‖x‖^2) S hc
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow,
    integral_const_mul, smul_eq_mul] at H
  have H' := congrArg (fun a : ℝ => c^(Module.finrank ℝ E)*a) H
  dsimp only at H'
  rw [← mul_assoc (c^(Module.finrank ℝ E)) ((c^(Module.finrank ℝ E))⁻¹),
    mul_inv_cancel₀ (pow_ne_zero _ hc.ne'), one_mul] at H'
  rw [← H', pow_add]
  ring

theorem momentPerspective_scale (d v j c : ℝ)
    (hv : 0 ≤ v) (hj : 0 < j) (hc : 0 < c) :
    momentPerspective d (c^d*v) (c^(d+2)*j) = momentPerspective d v j := by
  have hp : 0 < c^d := Real.rpow_pos_of_pos hc _
  have hp2 : 0 < c^(d+2) := Real.rpow_pos_of_pos hc _
  rw [momentPerspective_eq_quotient d _ _ (mul_nonneg hp.le hv) (mul_pos hp2 hj),
    momentPerspective_eq_quotient d _ _ hv hj,
    Real.mul_rpow hp.le hv, Real.mul_rpow hp2.le hj.le,
    ← Real.rpow_mul hc.le, ← Real.rpow_mul hc.le,
    show d*(1+d/2) = (d+2)*(d/2) by ring]
  field_simp [(Real.rpow_pos_of_pos hc ((d+2)*(d/2))).ne',
    (Real.rpow_pos_of_pos hj (d/2)).ne']
  ring

theorem momentPerspective_scale_nonneg (d v j c : ℝ)
    (hv : 0 ≤ v) (hj : 0 ≤ j) (hc : 0 < c) :
    momentPerspective d (c^d*v) (c^(d+2)*j) = momentPerspective d v j := by
  rcases hj.eq_or_lt with h | h
  · rw [← h]
    simp [momentPerspective, powerPerspective]
  · exact momentPerspective_scale d v j c hv h hc

end D4.ConeAnalysis
