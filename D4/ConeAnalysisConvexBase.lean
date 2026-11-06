import D4.ConeAnalysisPyramidComparison
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Measure

/-! A compact convex base containing the origin in its interior has the
positive continuous radial function given by the inverse Minkowski gauge.
The associated radial body agrees with it almost everywhere. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped Topology

def gaugeRadius {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Set E) (u : sphere (0:E) 1) : ℝ := (gauge B u.1)⁻¹

theorem gaugeRadius_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Set E} (hb : Bornology.IsBounded B) (h0 : (0:E) ∈ interior B)
    (u : sphere (0:E) 1) : 0 < gaugeRadius B u := by
  apply inv_pos.2
  exact (gauge_pos (absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0))
    (NormedSpace.isVonNBounded_of_isBounded ℝ hb)).mpr
    (ne_of_mem_sphere u.2 one_ne_zero)

theorem gaugeRadius_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Set E} (hc : Convex ℝ B) (hb : Bornology.IsBounded B)
    (h0 : (0:E) ∈ interior B) : Continuous (gaugeRadius B) := by
  apply ((continuous_gauge hc (mem_interior_iff_mem_nhds.mp h0)).comp continuous_subtype_val).inv₀
  intro u
  have H := gaugeRadius_pos hb h0 u
  exact (inv_pos.mp H).ne'

theorem radialBody_gaugeRadius {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Set E} (hc : Convex ℝ B) (hb : Bornology.IsBounded B)
    (h0 : (0:E) ∈ interior B) : radialBody (gaugeRadius B) = interior B \ {0} := by
  ext x
  by_cases hx : x = 0
  · subst x
    constructor
    · rintro ⟨y, _, hy⟩
      exact False.elim (y.2 hy)
    · simp
  · let q := homeomorphUnitSphereProd E ⟨x,hx⟩
    have hrep : x = q.2.1 • q.1.1 := by
      exact (congrArg Subtype.val ((homeomorphUnitSphereProd E).symm_apply_apply ⟨x,hx⟩)).symm
    have hg : 0 < gauge B q.1.1 := inv_pos.mp (gaugeRadius_pos hb h0 q.1)
    have hgx : gauge B x = q.2.1 * gauge B q.1.1 := by
      rw [hrep, gauge_smul_of_nonneg q.2.2.le, smul_eq_mul]
    rw [mem_diff, mem_singleton_iff, and_iff_left hx,
      ← gauge_lt_one_iff_mem_interior hc (mem_interior_iff_mem_nhds.mp h0), hgx,
      hrep, mem_radialBody_smul]
    unfold gaugeRadius
    simpa only [one_div] using (lt_div_iff₀ hg : q.2.1 < 1/gauge B q.1.1 ↔ _)

theorem radialBody_gaugeRadius_ae {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {B : Set E}
    (hc : Convex ℝ B) (hb : Bornology.IsBounded B) (h0 : (0:E) ∈ interior B) :
    radialBody (gaugeRadius B) =ᵐ[μ] B := by
  have hz : ∀ᵐ x ∂μ, x ≠ (0:E) := by
    apply ae_iff.mpr
    simpa using (measure_singleton (0:E) : μ {0} = 0)
  have hf : ∀ᵐ x ∂μ, x ∉ frontier B := by
    apply ae_iff.mpr
    simpa using hc.addHaar_frontier μ
  rw [radialBody_gaugeRadius hc hb h0]
  filter_upwards [hz, hf] with x hx hxf
  apply propext
  constructor
  · exact fun h => interior_subset h.1
  · intro hxB
    refine ⟨?_, hx⟩
    by_contra hxi
    exact hxf ⟨subset_closure hxB, hxi⟩

theorem convexPyramid_perspective_comparison {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {B : Set E}
    (hc : Convex ℝ B) (hB : IsCompact B) (h0 : (0:E) ∈ interior B) :
    ConePerspective.momentPerspective (Module.finrank ℝ E+1)
      ((μ.prod volume).real (pyramid B))
      (∫ p in pyramid B, (‖p.1‖^2+p.2^2) ∂μ.prod volume) ≤
    profile (Module.finrank ℝ E+1)
      (profileConstant (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1)))
      ((Module.finrank ℝ E:ℝ)*μ.real (ball (0:E) 1))
      (∫ y in B, (1+‖y‖^2)^(-((Module.finrank ℝ E:ℝ)+1)/2) ∂μ) := by
  let ρ := gaugeRadius B
  have hρ : Continuous ρ := gaugeRadius_continuous hc hB.isBounded h0
  have hp : ∀ u, 0 < ρ u := gaugeRadius_pos hB.isBounded h0
  have he : radialBody ρ =ᵐ[μ] B := radialBody_gaugeRadius_ae μ hc hB.isBounded h0
  have hsub : radialBody ρ ⊆ B := by
    rw [radialBody_gaugeRadius hc hB.isBounded h0]
    exact diff_subset.trans interior_subset
  obtain ⟨M, hM, hb⟩ := hB.isBounded.subset_closedBall_lt 0 (0:E)
  have Hv : (μ.prod volume).real (pyramid (radialBody ρ)) =
      (μ.prod volume).real (pyramid B) := by
    rw [pyramid_volume μ (radialBody_measurable ρ hρ.measurable) hM.le (hsub.trans hb),
      pyramid_volume μ hB.measurableSet hM.le hb]
    congr 1
    exact congrArg ENNReal.toReal (measure_congr he)
  have Hj : (∫ p in pyramid (radialBody ρ), (‖p.1‖^2+p.2^2) ∂μ.prod volume) =
      ∫ p in pyramid B, (‖p.1‖^2+p.2^2) ∂μ.prod volume := by
    rw [pyramid_secondMoment μ (radialBody_measurable ρ hρ.measurable) hM.le (hsub.trans hb),
      pyramid_secondMoment μ hB.measurableSet hM.le hb, setIntegral_congr_set he]
    congr 1
    congr 1
    exact congrArg ENNReal.toReal (measure_congr he)
  have H := radialPyramid_perspective_comparison μ ρ hρ hp
  rw [Hv, Hj, setIntegral_congr_set he] at H
  exact H

end D4.ConeAnalysis
