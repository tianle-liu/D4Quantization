import D4.ConeAnalysisFacetCoordinates
import D4.ConeAnalysisProjection
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! Solid angle is the actual spherical Haar measure of the set of
directions. Its relation to a unit-ball cap is proved from polar measure. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped Pointwise

theorem radial_spherical_cap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (h0 : (0:E) ∉ C)
    (hscale : ∀ (c : ℝ), 0 < c → ∀ x : E, c • x ∈ C ↔ x ∈ C) :
    Ioo (0:ℝ) 1 • (Subtype.val '' {u : sphere (0:E) 1 | (u:E) ∈ C}) =
      C ∩ ball (0:E) 1 := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨(hscale r hr.1 u).2 hu, ?_⟩
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1,
      mem_sphere_zero_iff_norm.mp u.2, mul_one]
    exact hr.2
  · rintro ⟨hxC, hx⟩
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ hxC)
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let u : sphere (0:E) 1 := ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']⟩
    refine ⟨‖x‖, ⟨hn, mem_ball_zero_iff.mp hx⟩, (u:E), ?_, ?_⟩
    · exact ⟨u, (hscale ‖x‖⁻¹ (inv_pos.2 hn) x).2 hxC, rfl⟩
    · exact smul_inv_smul₀ hn.ne' x

theorem sphericalMeasure_eq_dim_cap {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (C : Set E) (hC : MeasurableSet C) (h0 : (0:E) ∉ C)
    (hscale : ∀ (c : ℝ), 0 < c → ∀ x : E, c • x ∈ C ↔ x ∈ C) :
    μ.toSphere.real {u : sphere (0:E) 1 | (u:E) ∈ C} =
      (Module.finrank ℝ E:ℝ) * μ.real (C ∩ ball (0:E) 1) := by
  have hs : MeasurableSet {u : sphere (0:E) 1 | (u:E) ∈ C} :=
    hC.preimage measurable_subtype_coe
  rw [measureReal_def, toSphere_apply' μ hs,
    radial_spherical_cap C h0 hscale, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  rfl

end D4.ConeAnalysis
