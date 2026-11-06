import D4.FullRankLattice
import D4.GeometricTheoremB

noncomputable section
namespace D4.Euclidean
open MeasureTheory

theorem normalizedCellMoment_eq_latticeNormalizedMoment (L : Submodule ℤ Point) :
    FacetGeometry.normalizedCellMoment L = latticeNormalizedMoment L := by
  unfold FacetGeometry.normalizedCellMoment ConePerspective.normalizedMoment
    latticeNormalizedMoment
  change (∫ x in latticeCell L, ‖x‖^2) /
    ((Module.finrank ℝ Point:ℝ) * (volume (latticeCell L)).toReal ^
      (1+2/(Module.finrank ℝ Point:ℝ))) = _
  norm_num [Point,finrank_euclideanSpace]

end D4.Euclidean
