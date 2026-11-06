import D4.ConeAnalysisPyramidComparison
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The radial projection formula is proved by slicing a cone cut by the
Euclidean unit ball and then changing the height variable. -/
noncomputable section
set_option maxHeartbeats 800000
namespace D4.ConeAnalysis
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped Pointwise

theorem truncated_height_integral (k : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    (∫ t in Ioo (0:ℝ) 1, t^k * (if t^2*B < 1 then 1 else 0)) =
      B^(-((k:ℝ)+1)/2)/((k:ℝ)+1) := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  let c := (Real.sqrt B)⁻¹
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.2 hB0
  have hc : 0 < c := inv_pos.2 hs
  have hc1 : c ≤ 1 := by
    apply (inv_le_one₀ hs).2
    exact (Real.one_le_sqrt).2 hB
  have hsq : c^2*B = 1 := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hB0.le, inv_mul_cancel₀ hB0.ne']
  have hiff (t : ℝ) (ht : 0 ≤ t) : t^2*B < 1 ↔ t < c := by
    rw [← hsq]
    rw [mul_lt_mul_iff_of_pos_right hB0, sq_lt_sq₀ ht hc.le]
  have he : (∫ t in Ioo (0:ℝ) 1, t^k * (if t^2*B < 1 then 1 else 0)) =
      ∫ t in Ioo (0:ℝ) 1, (Iio c).indicator (fun t => t^k) t := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    simp only [hiff t ht.1.le]
    by_cases ht' : t < c <;> simp [Set.indicator, ht']
  rw [he, setIntegral_indicator measurableSet_Iio]
  have hset : Ioo (0:ℝ) 1 ∩ Iio c = Ioo 0 c := by
    ext t
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1,h.2.trans_le hc1⟩,h.2⟩⟩
  rw [hset, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hc.le, integral_pow]
  simp only [zero_pow (by omega : k+1 ≠ 0), sub_zero]
  congr 1
  have hce : c = B^(-(1:ℝ)/2) := by
    dsimp [c]
    rw [Real.sqrt_eq_rpow, show -(1:ℝ)/2 = -(1/2) by ring, Real.rpow_neg hB0.le]
  rw [hce, ← Real.rpow_natCast, ← Real.rpow_mul hB0.le]
  congr 1
  push_cast
  ring

private theorem integral_pyramid_slices_integrable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {B : Set E} (hB : MeasurableSet B)
    (f : E × ℝ → ℝ) (hf : IntegrableOn f (pyramid B) (μ.prod volume)) :
    (∫ p in pyramid B, f p ∂μ.prod volume) =
      ∫ t in Ioo (0:ℝ) 1, ∫ y in t • B, f (y,t) ∂μ := by
  rw [← integral_indicator (pyramid_measurable hB),
    integral_prod_symm _ (hf.integrable_indicator (pyramid_measurable hB)),
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

def unitBallCut {E : Type*} [NormedAddCommGroup E] : Set (E × ℝ) :=
  {p | ‖p.1‖^2+p.2^2 < 1}

def cappedPyramid {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Set E) : Set (E × ℝ) := pyramid B ∩ unitBallCut

theorem cappedPyramid_volume {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {B : Set E} (hB : MeasurableSet B)
    {M : ℝ} (hM : 0 ≤ M) (hb : B ⊆ closedBall (0:E) M) :
    (μ.prod volume).real (cappedPyramid B) =
      (∫ y in B, (1+‖y‖^2)^(-((Module.finrank ℝ E:ℝ)+1)/2) ∂μ) /
        ((Module.finrank ℝ E:ℝ)+1) := by
  let k := Module.finrank ℝ E
  have hcut : MeasurableSet (unitBallCut (E:=E)) :=
    (isOpen_lt (continuous_fst.norm.pow 2 |>.add (continuous_snd.pow 2)) continuous_const).measurableSet
  let f : E × ℝ → ℝ := unitBallCut.indicator (fun _ => 1)
  have hf : IntegrableOn f (pyramid B) (μ.prod volume) :=
    (((continuous_const.continuousOn.integrableOn_compact
      ((isCompact_closedBall (0:E) M).prod isCompact_Icc)).mono_set
        (pyramid_subset hM hb) : IntegrableOn (fun _ => (1:ℝ)) (pyramid B) (μ.prod volume))).indicator hcut
  have H := integral_pyramid_slices_integrable μ hB f hf
  have Hleft : (∫ p in pyramid B, f p ∂μ.prod volume) =
      (μ.prod volume).real (cappedPyramid B) := by
    rw [show f = unitBallCut.indicator (fun _ => (1:ℝ)) from rfl, setIntegral_indicator hcut]
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, cappedPyramid]
  rw [Hleft] at H
  let S : Set (E × ℝ) := {p | p.2^2*(1+‖p.1‖^2) < 1}
  let G : E × ℝ → ℝ := S.indicator (fun p => p.2^k)
  have hS : MeasurableSet S :=
    (isOpen_lt ((continuous_snd.pow 2).mul (continuous_const.add (continuous_fst.norm.pow 2)))
      continuous_const).measurableSet
  have hG : Integrable G ((μ.restrict B).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    apply Integrable.indicator _ hS
    apply ((continuous_snd.pow k).continuousOn.integrableOn_compact
      ((isCompact_closedBall (0:E) M).prod (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)))).mono_set
    exact Set.prod_mono hb Ioo_subset_Icc_self
  have hscale : ∀ t ∈ Ioo (0:ℝ) 1,
      (∫ y in t • B, f (y,t) ∂μ) = ∫ y in B, G (y,t) ∂μ := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have HH := setIntegral_comp_smul_of_pos μ (fun y => f (y,t)) B ht0
    have he : (fun y => f (t • y,t)) =
        fun y => if t^2*(1+‖y‖^2) < 1 then (1:ℝ) else 0 := by
      funext y
      dsimp [f, unitBallCut, Set.indicator]
      have heq : ‖t • y‖^2+t^2 = t^2*(1+‖y‖^2) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, mul_pow]
        ring
      simp only [heq]
    dsimp only at HH
    rw [he, smul_eq_mul] at HH
    have HH' := congrArg (fun a : ℝ => t^k*a) HH
    change t^k*_ = t^k*((t^k)⁻¹*_) at HH'
    rw [← mul_assoc (t^k) ((t^k)⁻¹), mul_inv_cancel₀ (pow_ne_zero _ ht0.ne'), one_mul] at HH'
    rw [← HH', ← integral_const_mul]
    apply setIntegral_congr_fun hB
    intro y _
    simp only [G, S, Set.indicator, mem_setOf_eq, mul_ite, mul_one, mul_zero]
  rw [H]
  calc
    (∫ t in Ioo (0:ℝ) 1, ∫ y in t • B, f (y,t) ∂μ) =
        ∫ t in Ioo (0:ℝ) 1, ∫ y in B, G (y,t) ∂μ :=
      setIntegral_congr_fun measurableSet_Ioo hscale
    _ = ∫ y in B, (∫ t in Ioo (0:ℝ) 1, G (y,t)) ∂μ :=
      (integral_integral_swap (f:=fun y t => G (y,t)) hG).symm
    _ = ∫ y in B, (1+‖y‖^2)^(-((k:ℝ)+1)/2)/((k:ℝ)+1) ∂μ := by
      apply setIntegral_congr_fun hB
      intro y _
      convert truncated_height_integral k (1+‖y‖^2) (by nlinarith [sq_nonneg ‖y‖]) using 1
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t _
      simp only [G, S, Set.indicator, mem_setOf_eq, mul_ite, mul_one, mul_zero]
    _ = _ := integral_div _ _

end D4.ConeAnalysis
