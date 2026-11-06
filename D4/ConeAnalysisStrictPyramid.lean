import D4.ConePerspectiveStrict
import D4.ConeAnalysisConvexBase

/-! Strict pyramid comparison for a nonconstant continuous radial function. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory ConePerspective

theorem radialPyramid_perspective_comparison_strict {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ρ : sphere (0:E) 1 → ℝ) (hρ : Continuous ρ) (hp : ∀ u, 0 < ρ u)
    (hne : ∃ u v, ρ u ≠ ρ v) :
    momentPerspective (Module.finrank ℝ E+1)
      ((μ.prod volume).real (pyramid (radialBody ρ)))
      (∫ p in pyramid (radialBody ρ), (‖p.1‖^2+p.2^2) ∂μ.prod volume) <
    profile (Module.finrank ℝ E+1)
      (profileConstant (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1)))
      ((Module.finrank ℝ E:ℝ)*μ.real (ball (0:E) 1))
      (∫ y in radialBody ρ, (1+‖y‖^2)^(-((Module.finrank ℝ E:ℝ)+1)/2) ∂μ) := by
  letI : Nonempty (sphere (0:E) 1) := (NormedSpace.sphere_nonempty.mpr zero_le_one).coe_sort
  obtain ⟨u, _, humax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hρ.continuousOn
  have hb : ∀ v, ρ v ≤ ρ u := fun v => humax (mem_univ v)
  rw [radialPyramid_volume_expectation μ ρ hρ.measurable hp (ρ u) (hp u) hb,
    radialPyramid_secondMoment_expectation μ ρ hρ hp (ρ u) (hp u) hb,
    radialBody_angle_expectation μ ρ hρ.measurable hp (ρ u) (hp u) hb]
  have hn : 2 ≤ Module.finrank ℝ E+1 := by
    have := Module.finrank_pos (R:=ℝ) (M:=E)
    omega
  have H := radial_average_comparison_strict (uniformSphere μ) (Module.finrank ℝ E+1) hn
    (μ.real (ball (0:E) 1)) (unitBall_measure_pos μ) ρ hρ hp hne
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using H


theorem convexPyramid_perspective_comparison_strict {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {B : Set E}
    (hc : Convex ℝ B) (hB : IsCompact B) (h0 : (0:E) ∈ interior B)
    (hne : ∃ u v, gaugeRadius B u ≠ gaugeRadius B v) :
    ConePerspective.momentPerspective (Module.finrank ℝ E+1)
      ((μ.prod volume).real (pyramid B))
      (∫ p in pyramid B, (‖p.1‖^2+p.2^2) ∂μ.prod volume) <
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
  have H := radialPyramid_perspective_comparison_strict μ ρ hρ hp hne
  rw [Hv, Hj, setIntegral_congr_set he] at H
  exact H


end D4.ConeAnalysis
