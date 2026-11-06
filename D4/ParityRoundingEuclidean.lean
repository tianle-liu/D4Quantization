import D4.ParityRounding
import D4.CubicQuantizerApplication

noncomputable section
namespace D4.Quantizer
open Analytic
attribute [local instance] Classical.propDecidable

theorem squaredError_eq_euclidean_norm (x : Vec) (z : IntVec) :
    squaredError x z =
      ‖Euclidean.realization (1:Gram) x - Euclidean.realization (1:Gram) (castVec z)‖^2 := by
  rw [← Euclidean.realization_sub,Euclidean.norm_sq_realization]
  simpa [Euclidean.gram] using (quadratic_one_sub_eq_squaredError x z).symm

/-- The rounding-and-parity algorithm minimizes the genuine Euclidean distance
among all points of the even-integer lattice. -/
theorem rounding_algorithm_euclidean (x : Vec) :
    ∃ i : Fin 4, |residual x i| = ‖residual x‖ ∧
      let z := if rounded x ∈ evenSumLattice then rounded x else rounded x+correction x i
      z ∈ evenSumLattice ∧ ∀ w : IntVec, w ∈ evenSumLattice →
        ‖Euclidean.realization (1:Gram) x - Euclidean.realization (1:Gram) (castVec z)‖ ≤
        ‖Euclidean.realization (1:Gram) x - Euclidean.realization (1:Gram) (castVec w)‖ := by
  obtain ⟨i,hi,hz,hmin⟩ := rounding_algorithm_total x
  refine ⟨i,hi,hz,fun w hw => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [← squaredError_eq_euclidean_norm] using hmin w hw

end D4.Quantizer
