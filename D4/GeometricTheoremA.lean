import D4.EuclideanSimilarity
import D4.GlobalReduction

/-!
The matrix theorem implies the full statement for arbitrary discrete full-rank
lattices, with actual Euclidean Voronoi integration and actual similarities.
The moment identities are explicit arguments to this modular implication.
CompleteTheoremA provides the unconditional statement.
-/
noncomputable section
namespace D4.Euclidean
open Analytic

theorem geometricTheoremA_of_matrixTheorem (hA : TheoremATarget)
    (L : Submodule ℤ Point) [DiscreteTopology L] [IsZLattice ℝ L] :
    optimalConstant ≤ latticeNormalizedMoment L ∧
      (latticeNormalizedMoment L = optimalConstant ↔
        SimilarLattices (lattice (basisMatrix ℝ)) (L : Set Point)) := by
  have hB := latticeBasisMatrix_det_ne_zero L
  have h := hA (gram (latticeBasisMatrix L)) (gram_posDef_of_det_ne_zero hB)
  rw [latticeNormalizedMoment_eq]
  rw [← latticeBasisMatrix_lattice L, ← similarD4Gram_iff_similarLattices hB]
  exact h

theorem geometricTheoremA_of_moments (hM : GeometricMomentIdentities)
    (L : Submodule ℤ Point) [DiscreteTopology L] [IsZLattice ℝ L] :
    optimalConstant ≤ latticeNormalizedMoment L ∧
      (latticeNormalizedMoment L = optimalConstant ↔
        SimilarLattices (lattice (basisMatrix ℝ)) (L : Set Point)) :=
  geometricTheoremA_of_matrixTheorem (theoremA_of_moments hM) L

end D4.Euclidean
