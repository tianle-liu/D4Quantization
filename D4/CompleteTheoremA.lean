import D4.SecondaryClosedMoment
import D4.GeometricTheoremA
import D4.LatticeMomentCompatibility

/-! Theorem A with all geometric moment premises discharged. -/
noncomputable section
namespace D4
open Analytic

/-- The three closed-cone identities are actual Voronoi integral identities. -/
theorem geometricMomentIdentities : GeometricMomentIdentities where
  principal := Principal.principal_closed_formula
  secondary2 := Secondary.secondary2_closed_formula
  secondary3 := Secondary.secondary3_closed_formula

/-- Global optimality and equality characterization for every positive-definite
four-dimensional Gram matrix. -/
theorem theoremA : TheoremATarget := theoremA_of_moments geometricMomentIdentities

namespace Euclidean
open MeasureTheory

/-- The theorem for actual full-rank Euclidean lattices, with the usual
similarity relation (positive scaling and an orthogonal linear map). -/
theorem geometricTheoremA (L : Submodule ℤ Point)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    optimalConstant ≤ FacetGeometry.normalizedCellMoment L ∧
      (FacetGeometry.normalizedCellMoment L = optimalConstant ↔
        SimilarLattices (lattice (basisMatrix ℝ)) (L : Set Point)) := by
  rw [normalizedCellMoment_eq_latticeNormalizedMoment]
  exact geometricTheoremA_of_matrixTheorem theoremA L

end Euclidean
end D4
