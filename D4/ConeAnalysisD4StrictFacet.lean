import D4.ConeAnalysisD4FullRank
import D4.ConeAnalysisStrictFacet

/-! Every actual octahedral D4 facet gives a strict circular-cone comparison. -/
noncomputable section
namespace D4.PhysicalD4
open Set Metric MeasureTheory Euclidean FacetGeometry ConeAnalysis

/-- Strictness is derived from the actual octahedral face, with no radial
nonconstancy or lattice hypothesis left to discharge. -/
theorem facet_pyramid_comparison_strict {z : Point} (hz : IsFacetVector lattice z) :
    ConePerspective.momentPerspective 4
      (volume.real (FacetGeometry.pyramid lattice z))
      (∫ x in FacetGeometry.pyramid lattice z, ‖x‖^2) <
    profile 4 (profileConstant 4 (dimensionBallVolume 3))
      (3*dimensionBallVolume 3) (facetSolidAngle lattice z) := by
  have hd : Module.finrank ℝ Point=4 := by simp [Point]
  have hdim : 2 ≤ Module.finrank ℝ Point := by omega
  have H := facet_pyramid_dimension_comparison_strict hz hdim
    (normalized_facet_base_radial_nonconstant hz)
  simpa only [hd,show 4-1=3 by omega,show (4:ℝ)-1=3 by norm_num,
    Nat.cast_ofNat] using H

/-- In particular, the explicit standard D4 facet is strictly worse than
its circular-cone comparator in the moment perspective. -/
theorem standard_facet_pyramid_comparison_strict :
    ConePerspective.momentPerspective 4
      (volume.real (FacetGeometry.pyramid lattice standardRoot))
      (∫ x in FacetGeometry.pyramid lattice standardRoot, ‖x‖^2) <
    profile 4 (profileConstant 4 (dimensionBallVolume 3))
      (3*dimensionBallVolume 3) (facetSolidAngle lattice standardRoot) :=
  facet_pyramid_comparison_strict standardRoot_isFacet

end D4.PhysicalD4
