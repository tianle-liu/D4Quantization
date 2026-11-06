import D4.ConeAnalysisGeometry
import D4.ConeAnalysisSphereMeasure
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Actual pyramids above bounded measurable bases. Their volume and
second moment are derived by Fubini and Haar scaling. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped Pointwise

def pyramid {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Set E) : Set (E × ℝ) :=
  {p | p.2 ∈ Ioo (0:ℝ) 1 ∧ p.2⁻¹ • p.1 ∈ B}

theorem pyramid_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {B : Set E} (hB : MeasurableSet B) :
    MeasurableSet (pyramid B) := by
  exact (measurable_snd measurableSet_Ioo).inter
    (hB.preimage (measurable_snd.inv.smul measurable_fst))

theorem pyramid_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Set E} {M : ℝ} (hM : 0 ≤ M) (hB : B ⊆ closedBall (0:E) M) :
    pyramid B ⊆ closedBall (0:E) M ×ˢ Icc (0:ℝ) 1 := by
  intro p hp
  have ht : 0 < p.2 := hp.1.1
  have hy : ‖p.2⁻¹ • p.1‖ ≤ M := mem_closedBall_zero_iff.mp (hB hp.2)
  refine ⟨?_, ⟨hp.1.1.le, hp.1.2.le⟩⟩
  rw [mem_closedBall_zero_iff]
  calc
    ‖p.1‖ = ‖p.2 • (p.2⁻¹ • p.1)‖ := by rw [smul_inv_smul₀ ht.ne']
    _ = p.2 * ‖p.2⁻¹ • p.1‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    _ ≤ p.2*M := mul_le_mul_of_nonneg_left hy ht.le
    _ ≤ M := mul_le_of_le_one_left hM hp.1.2.le

theorem integral_pyramid_slices {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {B : Set E} (hB : MeasurableSet B)
    {M : ℝ} (hM : 0 ≤ M) (hb : B ⊆ closedBall (0:E) M)
    (f : E × ℝ → ℝ) (hf : Continuous f) :
    (∫ p in pyramid B, f p ∂μ.prod volume) =
      ∫ t in Ioo (0:ℝ) 1, ∫ y in t • B, f (y,t) ∂μ := by
  have hfi : IntegrableOn f (pyramid B) (μ.prod volume) :=
    (hf.continuousOn.integrableOn_compact
      ((isCompact_closedBall _ _).prod isCompact_Icc)).mono_set (pyramid_subset hM hb)
  rw [← integral_indicator (pyramid_measurable hB),
    integral_prod_symm _ (hfi.integrable_indicator (pyramid_measurable hB)),
    ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    by_cases ht : t ∈ Ioo (0:ℝ) 1
    · rw [indicator_of_mem ht]
      dsimp only
      rw [← integral_indicator (hB.const_smul_of_ne_zero ht.1.ne')]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp only
        by_cases hy : y ∈ t • B
        · have hp : (y,t) ∈ pyramid B :=
            ⟨ht, (mem_smul_set_iff_inv_smul_mem₀ ht.1.ne' B y).mp hy⟩
          rw [indicator_of_mem hp, indicator_of_mem hy]
        · have hp : (y,t) ∉ pyramid B := fun hp =>
            hy ((mem_smul_set_iff_inv_smul_mem₀ ht.1.ne' B y).mpr hp.2)
          rw [indicator_of_not_mem hp, indicator_of_not_mem hy]
    · change ¬(0 < t ∧ t < 1) at ht
      simp [pyramid, Set.indicator, ht]

theorem pyramid_volume {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {B : Set E} (hB : MeasurableSet B)
    {M : ℝ} (hM : 0 ≤ M) (hb : B ⊆ closedBall (0:E) M) :
    (μ.prod volume).real (pyramid B) = μ.real B/(Module.finrank ℝ E+1) := by
  have H := integral_pyramid_slices μ hB hM hb (fun _ => (1:ℝ)) continuous_const
  simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
    Measure.restrict_apply MeasurableSet.univ, univ_inter] at H
  rw [measureReal_def, H]
  have hi : (∫ t in Ioo (0:ℝ) 1, (μ (t • B)).toReal) =
      ∫ t in Ioo (0:ℝ) 1, t^(Module.finrank ℝ E)*μ.real B := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [addHaar_smul_of_nonneg μ ht.1.le B, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg ht.1.le _), measureReal_def]
  rw [hi, integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_pow]
  simp only [one_pow, zero_pow (by omega : Module.finrank ℝ E+1 ≠ 0), sub_zero]
  ring

theorem pyramid_secondMoment {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {B : Set E} (hB : MeasurableSet B)
    {M : ℝ} (hM : 0 ≤ M) (hb : B ⊆ closedBall (0:E) M) :
    (∫ p in pyramid B, (‖p.1‖^2+p.2^2) ∂μ.prod volume) =
      ((∫ y in B, ‖y‖^2 ∂μ)+μ.real B)/(Module.finrank ℝ E+3) := by
  let k := Module.finrank ℝ E
  have hf : Continuous (fun p : E × ℝ => ‖p.1‖^2+p.2^2) := by fun_prop
  rw [integral_pyramid_slices μ hB hM hb _ hf]
  have hi : (∫ t in Ioo (0:ℝ) 1, ∫ y in t • B, (‖y‖^2+t^2) ∂μ) =
      ∫ t in Ioo (0:ℝ) 1, t^(k+2)*((∫ y in B, ‖y‖^2 ∂μ)+μ.real B) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    have ht0 : 0 < t := ht.1
    have hy : IntegrableOn (fun y : E => ‖y‖^2) B μ :=
      ((continuous_norm.pow 2).continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)).mono_set hb
    have hc : IntegrableOn (fun _ : E => (1:ℝ)) B μ :=
      (continuous_const.continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)).mono_set hb
    have H := setIntegral_comp_smul_of_pos μ (fun y : E => ‖y‖^2+t^2) B ht0
    dsimp only at H
    have Hleft : (∫ y in B, (‖t • y‖^2+t^2) ∂μ) =
        t^2*((∫ y in B, ‖y‖^2 ∂μ)+μ.real B) := by
      simp_rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, mul_pow]
      have hc' : IntegrableOn (fun _ : E => t^2) B μ := by
        simpa only [mul_one] using hc.const_mul (t^2)
      rw [integral_add (hy.const_mul (t^2)) hc', integral_const_mul]
      simp only [integral_const, smul_eq_mul, measureReal_def,
        Measure.restrict_apply MeasurableSet.univ, univ_inter]
      ring
    rw [Hleft, smul_eq_mul] at H
    have H' := congrArg (fun z : ℝ => t^k*z) H
    have htk : t^k ≠ 0 := pow_ne_zero _ ht0.ne'
    change t^k*(t^2*_) = t^k*((t^k)⁻¹*_) at H'
    rw [← mul_assoc (t^k) ((t^k)⁻¹), mul_inv_cancel₀ htk, one_mul] at H'
    rw [← H', pow_add]
    ring
  rw [hi, integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_pow]
  simp only [one_pow, zero_pow (by omega : k+2+1 ≠ 0), sub_zero, Nat.cast_add, Nat.cast_ofNat]
  change (1/((k:ℝ)+2+1))*_ = _
  ring

end D4.ConeAnalysis
