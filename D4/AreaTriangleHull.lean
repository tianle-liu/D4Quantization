import D4.AreaTriangles
import D4.PrincipalSimplexHull

/-! Convex-hull semantics of actual planar triangles. -/
noncomputable section
namespace D4.AreaEnvelope
open Set Matrix

def triangleMatrix (a b : Plane) : PlaneMatrix := !![a 0,b 0;a 1,b 1]

theorem triangleMatrix_mulVec (a b x : Plane) :
    triangleMatrix a b *ᵥ x = x 0 • a + x 1 • b := by
  ext i
  fin_cases i <;> simp [triangleMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem affineTriangle_convex (B : PlaneMatrix) (c : Plane) :
    Convex ℝ (affineTriangle B c) := by
  have h := ((Principal.standardSimplex_convex 2 1).linear_image (Matrix.toLin' B)).translate c
  simpa only [affineTriangle,Set.image_image,Function.comp_def] using h

theorem affineTriangle_vertices (a b : Plane) (i : Fin 3) :
    (![0,a,b] : Fin 3 → Plane) i ∈ affineTriangle (triangleMatrix a b) 0 := by
  fin_cases i
  · refine ⟨0,?_,?_⟩
    · simp [Principal.standardSimplex]
    · simp
  · refine ⟨![1,0],?_,?_⟩
    · simp [Principal.standardSimplex,Fin.forall_fin_succ,Fin.sum_univ_succ]
    · simp [triangleMatrix_mulVec]
  · refine ⟨![0,1],?_,?_⟩
    · simp [Principal.standardSimplex,Fin.forall_fin_succ,Fin.sum_univ_succ]
    · simp [triangleMatrix_mulVec]

theorem affineTriangle_eq_convexHull (a b : Plane) :
    affineTriangle (triangleMatrix a b) 0 = convexHull ℝ ({0,a,b} : Set Plane) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    refine mem_convexHull_of_exists_fintype (![1-x 0-x 1,x 0,x 1] : Fin 3 → ℝ)
      (![0,a,b] : Fin 3 → Plane) ?_ ?_ ?_ ?_
    · intro i
      fin_cases i
      · have hs := hx.2
        simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hs
        change x 0+x 1 ≤ 1 at hs
        dsimp
        linarith
      · exact hx.1 0
      · exact hx.1 1
    · simp [Fin.sum_univ_succ]
    · intro i
      fin_cases i <;> simp
    · simp [Fin.sum_univ_succ,triangleMatrix_mulVec]
  · apply convexHull_min ?_ (affineTriangle_convex _ _)
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]; exact affineTriangle_vertices a b 0
    · rw [h]; exact affineTriangle_vertices a b 1
    · rw [h]; exact affineTriangle_vertices a b 2

end D4.AreaEnvelope
