import D4.AreaIntegral

noncomputable section
namespace D4.AreaEnvelope
open MeasureTheory Set

theorem integral_positivePart_cube_on_compact (K : Set Plane) (hK : IsCompact K)
    (d : Plane → ℝ) (hd : ContinuousOn d K) (hn : ∀ x ∈ K, 0 ≤ d x)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ x in K, (max (t-d x) 0)^3) =
      3 * ∫ s in Icc 0 t, (t-s)^2 * volume.real {x | x ∈ K ∧ d x ≤ s} := by
  classical
  let d' := K.indicator d
  have hm : Measurable d' := hd.measurable_piecewise continuousOn_const hK.measurableSet
  have hn' : ∀ x, 0 ≤ d' x := by
    intro x
    by_cases hx : x ∈ K
    · simpa only [d',indicator_of_mem hx] using hn x hx
    · simp [d',hx]
  haveI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have he := integral_positivePart_cube (volume.restrict K) d' hm hn' t ht
  have hl : (∫ x in K, (max (t-d' x) 0)^3) = ∫ x in K, (max (t-d x) 0)^3 := by
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    simp only [d',indicator_of_mem hx]
  have hr (s : ℝ) : (volume.restrict K).real {x | d' x ≤ s} =
      volume.real {x | x ∈ K ∧ d x ≤ s} := by
    rw [measureReal_restrict_apply' hK.measurableSet]
    congr 1
    ext x
    simp only [mem_inter_iff,mem_setOf_eq]
    constructor
    · intro hx
      exact ⟨hx.2,by simpa only [d',indicator_of_mem hx.2] using hx.1⟩
    · intro hx
      exact ⟨by simpa only [d',indicator_of_mem hx.1] using hx.2,hx.1⟩
  rw [hl] at he
  simpa only [hr] using he

/-- Both correction formulas in the area-integral lemma, for the actual
Lebesgue integrals on a compact planar region. -/
theorem areaIntegral_sublevel (K : Set Plane) (hK : IsCompact K) (R : ℝ) (hR : 0 ≤ R)
    (U d : Plane → ℝ) (hU : ContinuousOn U K) (hd : ContinuousOn d K)
    (hn : ∀ x ∈ K, 0 ≤ d x) (t : ℝ) (ht : 0 ≤ t)
    (hb : ∀ x ∈ K, |t-d x| ≤ R) :
    areaIntegral K R U d t - negativeAreaIntegral K R U d t =
      (15/8 : ℝ) * ∫ s in Icc 0 t,
        (t-s)^2 * volume.real {x | x ∈ K ∧ d x ≤ s} := by
  rw [areaIntegral_positivePart K hK R hR U d hU hd t hb,
    integral_positivePart_cube_on_compact K hK d hd hn t ht]
  ring

end D4.AreaEnvelope
