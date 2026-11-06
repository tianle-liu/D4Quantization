import D4.PrincipalFan

/-! Finite simplex certificates determine a genuine integral by inclusion,
pairwise null intersections, and exact total volume. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

theorem vertexSimplices_ae_cover {ι : Type*} [Fintype ι]
    (S : Set Vec) (hS : IsCompact S) (v : ι → Fin 5 → Vec)
    (hsub : ∀ i, vertexSimplex (v i) ⊆ S)
    (hinter : Pairwise fun i j => volume (vertexSimplex (v i) ∩ vertexSimplex (v j)) = 0)
    (hvol : (∑ i, volume (vertexSimplex (v i))) = volume S) :
    (⋃ i, vertexSimplex (v i)) =ᵐ[volume] S := by
  have hm (i : ι) := (vertexSimplex_compact (v i)).measurableSet
  have hv : volume (⋃ i, vertexSimplex (v i)) = volume S := by
    rw [measure_iUnion₀ hinter (fun i => (hm i).nullMeasurableSet), tsum_fintype, hvol]
  exact ae_eq_of_subset_of_measure_ge (Set.iUnion_subset hsub) hv.ge
    (MeasurableSet.iUnion hm).nullMeasurableSet hS.measure_lt_top.ne

theorem integral_eq_sum_vertexSimplices {ι : Type*} [Fintype ι]
    (S : Set Vec) (hS : IsCompact S) (v : ι → Fin 5 → Vec)
    (hsub : ∀ i, vertexSimplex (v i) ⊆ S)
    (hinter : Pairwise fun i j => volume (vertexSimplex (v i) ∩ vertexSimplex (v j)) = 0)
    (hvol : (∑ i, volume (vertexSimplex (v i))) = volume S)
    (f : Vec → ℝ) (hf : Continuous f) :
    (∫ x in S, f x) = ∑ i, ∫ x in vertexSimplex (v i), f x := by
  rw [← setIntegral_congr_set (vertexSimplices_ae_cover S hS v hsub hinter hvol)]
  rw [integral_iUnion_ae (fun i => (vertexSimplex_compact (v i)).measurableSet.nullMeasurableSet)
    hinter (hf.continuousOn.integrableOn_compact (isCompact_iUnion (fun i => vertexSimplex_compact (v i)))),
    tsum_fintype]

theorem quadratic_integral_eq_vertex_sum {ι : Type*} [Fintype ι]
    (S : Set Vec) (hS : IsCompact S) (v : ι → Fin 5 → Vec)
    (hv : ∀ i, (simplexMatrix (v i)).det ≠ 0)
    (hsub : ∀ i, vertexSimplex (v i) ⊆ S)
    (hinter : Pairwise fun i j => volume (vertexSimplex (v i) ∩ vertexSimplex (v j)) = 0)
    (hvol : (∑ i, volume (vertexSimplex (v i))) = volume S)
    {Q : Gram} (hQ : Q.IsHermitian) :
    (∫ x in S, quadratic Q x) = ∑ i,
      |(simplexMatrix (v i)).det| / 720 *
        (quadratic Q (∑ j, v i j) + ∑ j, quadratic Q (v i j)) := by
  rw [integral_eq_sum_vertexSimplices S hS v hsub hinter hvol _ (quadratic_continuous Q)]
  apply Finset.sum_congr rfl
  intro i _
  exact vertexSimplex_quadratic hQ (v i) (hv i)

end D4.Principal
