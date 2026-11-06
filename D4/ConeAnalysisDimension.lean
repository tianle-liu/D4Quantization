import D4.ConeAnalysisFacetBounds
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! A common dimensional constant for all tangent hyperplanes. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory D4.FacetGeometry

def dimensionBallVolume (k : ℕ) : ℝ :=
  volume.real (ball (0 : EuclideanSpace ℝ (Fin k)) 1)

theorem dimensionBallVolume_pos (k : ℕ) : 0 < dimensionBallVolume k :=
  unitBall_measure_pos volume

theorem unitBall_volume_eq_dimension {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
    [MeasurableSpace F] [BorelSpace F] :
    volume.real (ball (0:F) 1) = dimensionBallVolume (Module.finrank ℝ F) := by
  letI : Nonempty (Fin (Module.finrank ℝ F)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  simp only [dimensionBallVolume, measureReal_def, InnerProductSpace.volume_ball,
    finrank_euclideanSpace, Fintype.card_fin]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {z : E}

theorem tangent_unitBall_volume {z : E} (hz : z ≠ 0) (hd : 2 ≤ Module.finrank ℝ E) :
    volume.real (ball (0 : tangent z) 1) = dimensionBallVolume (Module.finrank ℝ E-1) := by
  have hdim := tangent_finrank hz
  have hpos : 0 < Module.finrank ℝ (tangent z) := by omega
  letI : Nontrivial (tangent z) := Module.finrank_pos_iff.mp hpos
  rw [unitBall_volume_eq_dimension, show Module.finrank ℝ (tangent z) = Module.finrank ℝ E-1 by omega]

theorem facet_pyramid_dimension_comparison (hz : IsFacetVector L z)
    (hd : 2 ≤ Module.finrank ℝ E) :
    ConePerspective.momentPerspective (Module.finrank ℝ E)
      (volume.real (D4.FacetGeometry.pyramid L z))
      (∫ x in D4.FacetGeometry.pyramid L z, ‖x‖^2) ≤
    profile (Module.finrank ℝ E)
      (profileConstant (Module.finrank ℝ E) (dimensionBallVolume (Module.finrank ℝ E-1)))
      (((Module.finrank ℝ E:ℝ)-1)*dimensionBallVolume (Module.finrank ℝ E-1))
      (facetSolidAngle L z) := by
  have H := facet_pyramid_spherical_comparison hz hd
  rw [tangent_unitBall_volume hz.2.1 hd] at H
  have he : (Module.finrank ℝ (tangent z):ℝ) = (Module.finrank ℝ E:ℝ)-1 := by
    have := tangent_finrank hz.2.1
    have he : (Module.finrank ℝ (tangent z):ℝ)+1 = (Module.finrank ℝ E:ℝ) := by exact_mod_cast this
    linarith
  rwa [he] at H

theorem facetSolidAngle_mem_dimension (hz : IsFacetVector L z)
    (hd : 2 ≤ Module.finrank ℝ E) :
    facetSolidAngle L z ∈ Ioo 0 (angle (Module.finrank ℝ E)
      (((Module.finrank ℝ E:ℝ)-1)*dimensionBallVolume (Module.finrank ℝ E-1)) (Real.pi/2)) := by
  have H := facetSolidAngle_mem hz hd
  rw [tangent_unitBall_volume hz.2.1 hd] at H
  have he : (Module.finrank ℝ (tangent z):ℝ) = (Module.finrank ℝ E:ℝ)-1 := by
    have := tangent_finrank hz.2.1
    have he : (Module.finrank ℝ (tangent z):ℝ)+1 = (Module.finrank ℝ E:ℝ) := by exact_mod_cast this
    linarith
  rwa [he] at H

end D4.ConeAnalysis
