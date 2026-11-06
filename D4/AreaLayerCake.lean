import D4.AreaSquareEnvelope

/-! The cubic positive-part layer-cake identity, with actual sublevel-set
measure. This form applies to the polygon in the area-integral lemma by
restricting Lebesgue measure to that polygon. -/
noncomputable section
namespace D4.AreaEnvelope
open MeasureTheory Set

def layerKernel (d t s : ℝ) : ℝ := if d ≤ s then (t-s)^2 else 0

theorem integral_layerKernel (d t : ℝ) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    (∫ s in Icc 0 t, layerKernel d t s) = (max (t-d) 0)^3/3 := by
  have he : layerKernel d t = (Ici d).indicator (fun s : ℝ => (t-s)^2) := by
    funext s
    simp only [layerKernel,Set.indicator,mem_Ici]
  have hi : Icc 0 t ∩ Ici d = Icc d t := by
    ext s
    simp only [mem_inter_iff,mem_Icc,mem_Ici]
    constructor
    · intro h
      exact ⟨h.2,h.1.2⟩
    · intro h
      exact ⟨⟨hd.trans h.1,h.2⟩,h.1⟩
  rw [he,setIntegral_indicator measurableSet_Ici,hi]
  by_cases hdt : d ≤ t
  · rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hdt,
      max_eq_left (sub_nonneg.mpr hdt)]
    have hp : (fun s : ℝ => (t-s)^2) = fun s => 1*s^2+(-2*t)*s+t^2 := by
      funext s
      ring
    rw [hp,integral_poly2]
    ring
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hdt),setIntegral_empty,
      max_eq_right (sub_nonpos.mpr (le_of_not_ge hdt))]
    norm_num

theorem integrable_layerKernel {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (d : X → ℝ) (hd : Measurable d) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun p : X × ℝ => layerKernel (d p.1) t p.2)
      (μ.prod (volume.restrict (Icc 0 t))) := by
  have hm : Measurable (fun p : X × ℝ => layerKernel (d p.1) t p.2) := by
    unfold layerKernel
    exact Measurable.ite (measurableSet_le (hd.comp measurable_fst) measurable_snd)
      ((measurable_const.sub measurable_snd).pow_const 2) measurable_const
  refine (integrable_const (t^2 : ℝ)).mono' hm.aestronglyMeasurable ?_
  have ha : ∀ᵐ p : X × ℝ ∂μ.prod (volume.restrict (Icc 0 t)), p.2 ∈ Icc 0 t := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)).mpr
    exact Filter.Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Icc
  filter_upwards [ha] with p hp
  unfold layerKernel
  split_ifs
  · rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith [hp.1,hp.2]
  · simp only [norm_zero]
    positivity

theorem integral_layerKernel_sublevel {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (d : X → ℝ) (hd : Measurable d) (t s : ℝ) :
    (∫ x, layerKernel (d x) t s ∂μ) = (t-s)^2 * μ.real {x | d x ≤ s} := by
  have he : (fun x => layerKernel (d x) t s) =
      {x | d x ≤ s}.indicator (fun _ => (t-s)^2) := by
    funext x
    simp only [layerKernel,Set.indicator,mem_setOf_eq]
  rw [he,integral_indicator_const _ (measurableSet_le hd measurable_const)]
  simp only [smul_eq_mul,mul_comm]

/-- A direct Fubini proof of the sublevel-set formula; no regularity of the
sublevel boundaries is required. -/
theorem integral_positivePart_cube {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (d : X → ℝ) (hd : Measurable d) (hn : ∀ x, 0 ≤ d x)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ x, (max (t-d x) 0)^3 ∂μ) =
      3 * ∫ s in Icc 0 t, (t-s)^2 * μ.real {x | d x ≤ s} := by
  have hs := integral_integral_swap (μ := μ) (ν := volume.restrict (Icc 0 t))
    (f := fun x s => layerKernel (d x) t s) (integrable_layerKernel μ d hd t ht)
  change (∫ x, ∫ s in Icc 0 t, layerKernel (d x) t s ∂volume ∂μ) =
    ∫ s in Icc 0 t, ∫ x, layerKernel (d x) t s ∂μ at hs
  simp_rw [integral_layerKernel _ _ (hn _) ht,integral_layerKernel_sublevel μ d hd] at hs
  rw [integral_div] at hs
  linarith

end D4.AreaEnvelope
