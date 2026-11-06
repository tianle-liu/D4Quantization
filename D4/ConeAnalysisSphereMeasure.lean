import D4.ConeAnalysisRadialBody
import D4.ConePerspectiveRadial

/-! The uniform probability measure used in the radial-function Jensen
argument is explicitly obtained by normalizing Mathlib's Haar-induced
sphere measure. Its mass and integral normalization are proved. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory MeasureTheory.Measure

def uniformSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) : Measure (sphere (0:E) 1) :=
  (μ.toSphere univ)⁻¹ • μ.toSphere

instance uniformSphere_isProbabilityMeasure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] : IsProbabilityMeasure (uniformSphere μ) := by
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hpos : μ.toSphere univ ≠ 0 := by
    rw [toSphere_apply_univ]
    exact mul_ne_zero (by exact_mod_cast hn.ne') (measure_ball_pos μ (0:E) zero_lt_one).ne'
  constructor
  simp only [uniformSphere, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)

theorem integral_uniformSphere {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : sphere (0:E) 1 → ℝ) :
    (∫ u, f u ∂uniformSphere μ) =
      (∫ u, f u ∂μ.toSphere) /
        ((Module.finrank ℝ E:ℝ)*μ.real (ball (0:E) 1)) := by
  rw [uniformSphere, integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul]
  rw [← measureReal_def, toSphere_real_apply_univ]
  ring

theorem unitBall_measure_pos {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] : 0 < μ.real (ball (0:E) 1) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (measure_ball_pos μ (0:E) zero_lt_one).ne'
    (measure_ball_lt_top.ne)

/-- The radial body's true volume, written as an expectation over the
actual uniform measure on its sphere of directions. -/
theorem radialBody_volume_expectation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ρ : sphere (0:E) 1 → ℝ) (hρ : Measurable ρ)
    (hp : ∀ u, 0 < ρ u) (M : ℝ) (hM : 0 < M) (hb : ∀ u, ρ u ≤ M) :
    μ.real (radialBody ρ) =
      μ.real (ball (0:E) 1) * ∫ u, ρ u^(Module.finrank ℝ E) ∂uniformSphere μ := by
  have H := integral_norm_pow_radialBody μ 0 ρ hρ hp M hM hb
  simp only [pow_zero, integral_const, smul_eq_mul, mul_one, Nat.add_zero, Nat.cast_zero,
    add_zero, measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter] at H
  rw [integral_uniformSphere]
  have hκ := unitBall_measure_pos μ
  have hn : (0:ℝ) < Module.finrank ℝ E := by exact_mod_cast (Module.finrank_pos (R:=ℝ) (M:=E))
  have H' : μ.real (radialBody ρ) =
      (∫ u, ρ u^(Module.finrank ℝ E) ∂μ.toSphere)/(Module.finrank ℝ E) := by
    simpa only [measureReal_def] using H
  rw [H']
  field_simp
  ring

/-- The corresponding actual radial second moment. -/
theorem radialBody_secondMoment_expectation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ρ : sphere (0:E) 1 → ℝ) (hρ : Measurable ρ)
    (hp : ∀ u, 0 < ρ u) (M : ℝ) (hM : 0 < M) (hb : ∀ u, ρ u ≤ M) :
    (∫ x in radialBody ρ, ‖x‖^2 ∂μ) =
      ((Module.finrank ℝ E:ℝ)*μ.real (ball (0:E) 1)/(Module.finrank ℝ E+2)) *
        ∫ u, ρ u^(Module.finrank ℝ E+2) ∂uniformSphere μ := by
  rw [integral_norm_pow_radialBody μ 2 ρ hρ hp M hM hb, integral_uniformSphere]
  have hκ := unitBall_measure_pos μ
  have hn : (0:ℝ) < Module.finrank ℝ E := by exact_mod_cast (Module.finrank_pos (R:=ℝ) (M:=E))
  norm_num only [Nat.cast_ofNat]
  field_simp
  ring

theorem radialBody_angle_expectation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ρ : sphere (0:E) 1 → ℝ) (hρ : Measurable ρ)
    (hp : ∀ u, 0 < ρ u) (M : ℝ) (hM : 0 < M) (hb : ∀ u, ρ u ≤ M) :
    (∫ y in radialBody ρ, (1+‖y‖^2)^(-((Module.finrank ℝ E:ℝ)+1)/2) ∂μ) =
      ∫ u, radiusAngle (Module.finrank ℝ E+1)
        ((Module.finrank ℝ E:ℝ)*μ.real (ball (0:E) 1)) (ρ u) ∂uniformSphere μ := by
  let k := Module.finrank ℝ E
  let D := (k:ℝ)*μ.real (ball (0:E) 1)
  have hD : 0 < D := mul_pos (by exact_mod_cast (Module.finrank_pos (R:=ℝ) (M:=E)))
    (unitBall_measure_pos μ)
  let f : ℝ → ℝ := fun r => (1+r^2)^(-((k:ℝ)+1)/2)
  have hf : Continuous f := by
    exact (continuous_const.add (continuous_id.pow 2)).rpow_const (fun r => Or.inl (by positivity))
  rw [integral_radialBody_radial μ ρ hρ M hM hb f hf, integral_uniformSphere]
  have he : (fun u => radiusAngle (k+1) D (ρ u)) =
      fun u => D * ∫ r in Ioo (0:ℝ) (ρ u), r^(k-1)*f r := by
    funext u
    unfold radiusAngle radiusKernel
    rw [intervalIntegral.integral_of_le (hp u).le, integral_Ioc_eq_integral_Ioo]
    simp only [Nat.cast_add, Nat.cast_one, show k+1-2 = k-1 by omega]
    rfl
  change _ = (∫ u, radiusAngle (k+1) D (ρ u) ∂μ.toSphere)/D
  rw [he, integral_const_mul, mul_div_cancel_left₀ _ hD.ne']

end D4.ConeAnalysis
