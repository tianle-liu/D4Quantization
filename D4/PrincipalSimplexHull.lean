import D4.PrincipalSimplexVertices

/-! The integrated affine simplex is exactly the convex hull of its vertices. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

theorem standardSimplex_convex (n : ℕ) (r : ℝ) : Convex ℝ (standardSimplex n r) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_⟩
  change (∑ i, (a * x i + b * y i)) ≤ r
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    _ ≤ a * r + b * r := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
      (mul_le_mul_of_nonneg_left hy.2 hb)
    _ = r := by rw [← add_mul, hab, one_mul]

theorem vertexSimplex_convex (v : Fin 5 → Vec) : Convex ℝ (vertexSimplex v) := by
  have h := ((standardSimplex_convex 4 1).linear_image (Matrix.toLin' (simplexMatrix v))).translate (v 0)
  simpa only [Set.image_image, Function.comp_def] using h

theorem vertex_mem_vertexSimplex (v : Fin 5 → Vec) (i : Fin 5) : v i ∈ vertexSimplex v := by
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ⟨0, ?_, ?_⟩
    · simp [standardSimplex]
    · simp
  · refine ⟨Pi.single j 1, ?_, ?_⟩
    · constructor
      · intro k
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      · simp
    · change v 0 + simplexMatrix v *ᵥ Pi.single j 1 = v j.succ
      rw [Matrix.mulVec_single_one]
      ext k
      simp only [Pi.add_apply, Matrix.transpose_apply, simplexMatrix]
      ring

theorem vertexSimplex_eq_convexHull (v : Fin 5 → Vec) :
    vertexSimplex v = convexHull ℝ (Set.range v) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    let w : Fin 5 → ℝ := Fin.cons (1 - ∑ i, x i) x
    refine mem_convexHull_of_exists_fintype w v ?_ ?_ (fun i => ⟨i, rfl⟩) ?_
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sub_nonneg.mpr hx.2
      · exact hx.1 j
    · simp [w, Fin.sum_univ_succ]
    · ext k
      simp only [Fin.sum_univ_succ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        w, Fin.cons_zero, Fin.cons_succ, Pi.add_apply, Matrix.mulVec, dotProduct,
        simplexMatrix, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
      ring
  · exact convexHull_min (Set.range_subset_iff.mpr (vertex_mem_vertexSimplex v))
      (vertexSimplex_convex v)

theorem vertexSimplex_subset_of_vertices {S : Set Vec} (hS : Convex ℝ S)
    (v : Fin 5 → Vec) (hv : ∀ i, v i ∈ S) : vertexSimplex v ⊆ S := by
  rw [vertexSimplex_eq_convexHull]
  exact convexHull_min (Set.range_subset_iff.mpr hv) hS

end D4.Principal
