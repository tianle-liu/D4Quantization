import D4.ConeAnalysisStrictPyramid
import D4.ConeAnalysisDimension

/-! Strict comparison for an actual facet with a nonconstant radial function. -/
noncomputable section
set_option linter.unusedSectionVars false
namespace D4.ConeAnalysis
open Set Metric MeasureTheory D4.FacetGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem facet_pyramid_perspective_comparison_strict {L : Submodule ℤ E}
    [DiscreteTopology L] [IsZLattice ℝ L] {z : E}
    (hz : IsFacetVector L z) (hd : 2 ≤ Module.finrank ℝ E)
    (hne : ∃ u v, gaugeRadius (normalizedFacetBase L z) u ≠
      gaugeRadius (normalizedFacetBase L z) v) :
    ConePerspective.momentPerspective (Module.finrank ℝ E)
      (volume.real (D4.FacetGeometry.pyramid L z))
      (∫ x in D4.FacetGeometry.pyramid L z, ‖x‖^2) <
    profile (Module.finrank ℝ E)
      (profileConstant (Module.finrank ℝ E) (volume.real (ball (0 : tangent z) 1)))
      ((Module.finrank ℝ (tangent z):ℝ)*volume.real (ball (0 : tangent z) 1))
      (∫ y in normalizedFacetBase L z, (1+‖y‖^2)^(-(Module.finrank ℝ E:ℝ)/2)) := by
  have hdim := tangent_finrank hz.2.1
  have hpos : 0 < Module.finrank ℝ (tangent z) := by omega
  letI : Nontrivial (tangent z) := Module.finrank_pos_iff.mp hpos
  have he : (Module.finrank ℝ E:ℝ) = (Module.finrank ℝ (tangent z):ℝ)+1 := by
    exact_mod_cast hdim.symm
  rw [facet_pyramid_perspective L hz.2.1, ← hdim]
  simpa only [Nat.cast_add, Nat.cast_one] using convexPyramid_perspective_comparison_strict volume
    (normalizedFacetBase_convex L z) (normalizedFacetBase_compact L z)
    (normalizedFacetBase_zero_interior hz) hne

theorem facet_pyramid_spherical_comparison_strict {L : Submodule ℤ E}
    [DiscreteTopology L] [IsZLattice ℝ L] {z : E}
    (hz : IsFacetVector L z) (hd : 2 ≤ Module.finrank ℝ E)
    (hne : ∃ u v, gaugeRadius (normalizedFacetBase L z) u ≠
      gaugeRadius (normalizedFacetBase L z) v) :
    ConePerspective.momentPerspective (Module.finrank ℝ E)
      (volume.real (D4.FacetGeometry.pyramid L z))
      (∫ x in D4.FacetGeometry.pyramid L z, ‖x‖^2) <
    profile (Module.finrank ℝ E)
      (profileConstant (Module.finrank ℝ E) (volume.real (ball (0 : tangent z) 1)))
      ((Module.finrank ℝ (tangent z):ℝ)*volume.real (ball (0 : tangent z) 1))
      (facetSolidAngle L z) := by
  rw [facetSolidAngle_eq_base_integral L hz.2.1]
  exact facet_pyramid_perspective_comparison_strict hz hd hne

variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {z : E}
theorem facet_pyramid_dimension_comparison_strict (hz : IsFacetVector L z)
    (hd : 2 ≤ Module.finrank ℝ E)
    (hne : ∃ u v, gaugeRadius (normalizedFacetBase L z) u ≠
      gaugeRadius (normalizedFacetBase L z) v) :
    ConePerspective.momentPerspective (Module.finrank ℝ E)
      (volume.real (D4.FacetGeometry.pyramid L z))
      (∫ x in D4.FacetGeometry.pyramid L z, ‖x‖^2) <
    profile (Module.finrank ℝ E)
      (profileConstant (Module.finrank ℝ E) (dimensionBallVolume (Module.finrank ℝ E-1)))
      (((Module.finrank ℝ E:ℝ)-1)*dimensionBallVolume (Module.finrank ℝ E-1))
      (facetSolidAngle L z) := by
  have H := facet_pyramid_spherical_comparison_strict hz hd hne
  rw [tangent_unitBall_volume hz.2.1 hd] at H
  have he : (Module.finrank ℝ (tangent z):ℝ) = (Module.finrank ℝ E:ℝ)-1 := by
    have := tangent_finrank hz.2.1
    have he : (Module.finrank ℝ (tangent z):ℝ)+1 = (Module.finrank ℝ E:ℝ) := by exact_mod_cast this
    linarith
  rwa [he] at H

end D4.ConeAnalysis
