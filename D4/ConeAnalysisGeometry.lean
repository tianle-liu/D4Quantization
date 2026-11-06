import D4.ConeAnalysisPolar
import D4.ConePerspectiveProfile
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Genuine height-one circular-cone sets and their Euclidean coordinate
volume and second-moment integrals. The coordinate expression
`‖y‖² + t²` is the squared Euclidean norm under an orthogonal splitting. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory MeasureTheory.Measure

def circularCone {E : Type*} [NormedAddCommGroup E] (R : ℝ) : Set (E × ℝ) :=
  {p | p.2 ∈ Ioo (0:ℝ) 1 ∧ ‖p.1‖ < p.2*R}

theorem circularCone_measurable {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (R : ℝ) : MeasurableSet (circularCone (E:=E) R) := by
  exact (measurable_snd measurableSet_Ioo).inter
    (measurableSet_lt (continuous_fst.norm.measurable)
      (continuous_snd.mul continuous_const).measurable)

theorem circularCone_subset {E : Type*} [NormedAddCommGroup E]
    (R : ℝ) (hR : 0 ≤ R) : circularCone (E:=E) R ⊆ closedBall (0:E) R ×ˢ Icc (0:ℝ) 1 := by
  intro p hp
  exact ⟨by
    rw [mem_closedBall_zero_iff]
    exact hp.2.le.trans (mul_le_of_le_one_left hR hp.1.2.le), ⟨hp.1.1.le, hp.1.2.le⟩⟩

theorem integral_circularCone_slices {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (R : ℝ) (hR : 0 ≤ R)
    (f : E × ℝ → ℝ) (hf : Continuous f) :
    (∫ p in circularCone R, f p ∂μ.prod volume) =
      ∫ t in Ioo (0:ℝ) 1, ∫ y in ball (0:E) (t*R), f (y,t) ∂μ := by
  have hcompact : IsCompact (closedBall (0:E) R ×ˢ Icc (0:ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hfi : IntegrableOn f (circularCone R) (μ.prod volume) :=
    (hf.continuousOn.integrableOn_compact hcompact).mono_set (circularCone_subset R hR)
  rw [← integral_indicator (circularCone_measurable R),
    integral_prod_symm _ (hfi.integrable_indicator (circularCone_measurable R)),
    ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    by_cases ht : t ∈ Ioo (0:ℝ) 1
    · rw [indicator_of_mem ht, ← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        simp [circularCone, Set.indicator, ht.1, ht.2, mem_ball_zero_iff]
    · change ¬(0 < t ∧ t < 1) at ht
      simp [circularCone, Set.indicator, ht]

theorem circularCone_volume {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (R : ℝ) (hR : 0 ≤ R) :
    (μ.prod volume).real (circularCone (E:=E) R) =
      μ.real (ball (0:E) 1) * R^(Module.finrank ℝ E) / (Module.finrank ℝ E+1) := by
  have H := integral_circularCone_slices μ R hR (fun _ => (1:ℝ)) continuous_const
  simp only [integral_const, smul_eq_mul, mul_one] at H
  simp only [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter] at H
  have H' : (μ.prod volume).real (circularCone (E:=E) R) =
      ∫ t in Ioo (0:ℝ) 1, μ.real (ball (0:E) (t*R)) := by
    simpa only [measureReal_def] using H
  rw [H']
  have hi : (∫ t in Ioo (0:ℝ) 1, μ.real (ball (0:E) (t*R))) =
      ∫ t in Ioo (0:ℝ) 1, t^(Module.finrank ℝ E) *
        (R^(Module.finrank ℝ E)*μ.real (ball (0:E) 1)) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [← addHaar_real_closedBall_eq_addHaar_real_ball μ (0:E) (t*R),
      addHaar_real_closedBall μ _ (mul_nonneg ht.1.le hR), mul_pow]
    ring
  rw [hi, integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_pow]
  simp only [one_pow, zero_pow (by omega : Module.finrank ℝ E+1 ≠ 0), sub_zero]
  ring

theorem circularCone_secondMoment {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (R : ℝ) (hR : 0 ≤ R) :
    (∫ p in circularCone R, (‖p.1‖^2 + p.2^2) ∂μ.prod volume) =
      μ.real (ball (0:E) 1) * R^(Module.finrank ℝ E) /
        (Module.finrank ℝ E+3) *
        (1+(Module.finrank ℝ E:ℝ)/(Module.finrank ℝ E+2)*R^2) := by
  let n := Module.finrank ℝ E
  have hf : Continuous (fun p : E × ℝ => ‖p.1‖^2+p.2^2) := by fun_prop
  rw [integral_circularCone_slices μ R hR _ hf]
  have hi : (∫ t in Ioo (0:ℝ) 1, ∫ y in ball (0:E) (t*R), (‖y‖^2+t^2) ∂μ) =
      ∫ t in Ioo (0:ℝ) 1,
        t^(n+2) * (μ.real (ball (0:E) 1)*R^n*(1+(n:ℝ)/(n+2)*R^2)) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    have htR : 0 ≤ t*R := mul_nonneg ht.1.le hR
    have hy : IntegrableOn (fun y : E => ‖y‖^2) (ball (0:E) (t*R)) μ :=
      (((continuous_norm.pow 2).continuousOn).integrableOn_compact
        (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
    have hc : IntegrableOn (fun _ : E => t^2) (ball (0:E) (t*R)) μ :=
      (continuous_const.continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
    rw [integral_add hy hc, integral_norm_pow_ball μ 2 (t*R) htR,
      integral_const]
    simp only [smul_eq_mul, measureReal_def,
      Measure.restrict_apply MeasurableSet.univ, univ_inter]
    have hvol : (μ (ball (0:E) (t*R))).toReal = (t*R)^n*μ.real (ball (0:E) 1) := by
      rw [← measureReal_def, ← addHaar_real_closedBall_eq_addHaar_real_ball μ (0:E) (t*R),
        addHaar_real_closedBall μ _ htR]
    rw [hvol]
    simp only [mul_pow, pow_add]
    norm_num only [Nat.cast_ofNat]
    simp only [measureReal_def]
    dsimp only [n]
    ring
  rw [hi, integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_pow]
  simp only [one_pow, zero_pow (by omega : n+2+1 ≠ 0), sub_zero, Nat.cast_add, Nat.cast_ofNat]
  change (1/((n:ℝ)+2+1))*_ = _
  ring

theorem circularCone_volume_eq_formula {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (R : ℝ) (hR : 0 ≤ R) :
    (μ.prod volume).real (circularCone (E:=E) R) =
      coneVolume (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1)) R := by
  rw [circularCone_volume μ R hR]
  unfold coneVolume
  rw [add_sub_cancel_right, Real.rpow_natCast]
  ring

theorem circularCone_secondMoment_eq_formula {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (R : ℝ) (hR : 0 ≤ R) :
    (∫ p in circularCone R, (‖p.1‖^2 + p.2^2) ∂μ.prod volume) =
      coneMoment (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1)) R := by
  rw [circularCone_secondMoment μ R hR]
  unfold coneMoment coneVolume CircularCone.alpha
  rw [add_sub_cancel_right, Real.rpow_natCast]
  field_simp
  ring

/-- The angle integral is also an actual weighted integral over the
Euclidean base ball. This theorem does not identify the weight with
spherical surface measure; that is a separate projection formula. -/
theorem radiusAngle_eq_base_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (R : ℝ) (hR : 0 ≤ R) :
    radiusAngle (Module.finrank ℝ E+1)
      ((Module.finrank ℝ E:ℝ)*μ.real (ball (0:E) 1)) R =
    ∫ y in ball (0:E) R, (1+‖y‖^2)^(-((Module.finrank ℝ E:ℝ)+1)/2) ∂μ := by
  rw [integral_ball_radial μ R (fun t => (1+t^2)^(-((Module.finrank ℝ E:ℝ)+1)/2))]
  unfold radiusAngle radiusKernel
  rw [intervalIntegral.integral_of_le hR, integral_Ioc_eq_integral_Ioo]
  simp only [Nat.cast_add, Nat.cast_one,
    show Module.finrank ℝ E+1-2 = Module.finrank ℝ E-1 by omega]

end D4.ConeAnalysis
