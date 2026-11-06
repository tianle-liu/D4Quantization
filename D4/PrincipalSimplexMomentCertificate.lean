import D4.PrincipalSimplexCover
import D4.PrincipalDualRegion

/-! A finite, checkable simplex certificate for the genuine nearest-lattice
moment. Every analytic and measure-theoretic step is discharged here. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

def simplexMomentNumerator {ι : Type*} [Fintype ι] (Q : Gram) (v : ι → Fin 5 → Vec) : ℝ :=
  ∑ t, |(simplexMatrix (v t)).det| *
    (quadratic Q.adjugate (∑ j, v t j) + ∑ j, quadratic Q.adjugate (v t j))

theorem vertexSimplices_volume_sum {ι : Type*} [Fintype ι]
    {Q : Gram} (hQ : Q.PosDef) (v : ι → Fin 5 → Vec)
    (hv : ∀ i, (simplexMatrix (v i)).det ≠ 0)
    (hvol : (∑ i, |(simplexMatrix (v i)).det|) = 384 * Q.det) :
    (∑ i, volume (vertexSimplex (v i))) = volume (dualRegion Q) := by
  simp_rw [vertexSimplex_volume _ (hv _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (abs_nonneg _) (by norm_num)),
    dualRegion_volume hQ]
  congr 1
  rw [← Finset.sum_div, hvol]
  ring

/-- Finite all-integer vertex support, finite separating functionals, and
the exact determinant sum suffice to certify the actual integral. -/
theorem simplexMomentNumerator_eq_actual {ι : Type*} [Fintype ι]
    {Q : Gram} (hQ : Q.PosDef) (v : ι → Fin 5 → Vec)
    (hv : ∀ i, (simplexMatrix (v i)).det ≠ 0)
    (hsupport : ∀ i j, v i j ∈ dualRegion Q)
    (hinter : Pairwise fun i j => volume (vertexSimplex (v i) ∩ vertexSimplex (v j)) = 0)
    (hvol : (∑ i, |(simplexMatrix (v i)).det|) = 384 * Q.det) :
    simplexMomentNumerator Q v = 46080 * Q.det^2 * moment Q := by
  have hsub (i : ι) : vertexSimplex (v i) ⊆ dualRegion Q :=
    vertexSimplex_subset_of_vertices (dualRegion_convex Q) (v i) (hsupport i)
  have hi := quadratic_integral_eq_vertex_sum (dualRegion Q) (dualRegion_compact hQ) v hv
    hsub hinter (vertexSimplices_volume_sum hQ v hv hvol) hQ.isHermitian.adjugate
  have hscale : (∑ i, |(simplexMatrix (v i)).det| / 720 *
      (quadratic Q.adjugate (∑ j, v i j) + ∑ j, quadratic Q.adjugate (v i j))) =
        simplexMomentNumerator Q v / 720 := by
    rw [simplexMomentNumerator, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [dualRegion_adjugate_moment hQ, hscale] at hi
  nlinarith

end D4.Principal
