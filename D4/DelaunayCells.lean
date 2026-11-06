import D4.DelaunaySupport
import D4.DelaunaySupportData

noncomputable section
namespace D4.Delaunay
open Matrix Analytic Secondary
set_option maxHeartbeats 0

theorem principalIntegerGenerators_cast (k : Fin 10) :
    castVec (principalIntegerGenerators k)=cone1Vectors k := by
  ext i
  fin_cases k <;> fin_cases i <;>
    norm_num [castVec, principalIntegerGenerators, cone1Vectors]

theorem principal_normal_support (s : Fin 24) (k : Fin 10) :
    DualSupport (realMatrix (generators1 k)) (castVec (principalNormals s k)) := by
  rw [generators1_cast, ← principalIntegerGenerators_cast]
  rcases principal_normals_sign s k with h | h
  · rw [h]
    simpa using rankOne_support (principalIntegerGenerators k) 1 (Or.inl rfl)
  · rw [h]
    have hn : castVec (-principalIntegerGenerators k)=
        (-1:ℝ) • castVec (principalIntegerGenerators k) := by
      ext i
      simp [castVec]
    rw [hn]
    simpa only [Int.cast_neg, Int.cast_one] using
      rankOne_support (principalIntegerGenerators k) (-1) (Or.inr rfl)

theorem cells1_supported (w : Fin 10 → ℝ) (hw : ∀ k, 0 ≤ w k) (s : Fin 24) :
    SupportsSimplex (principalForm w) (cells1 s)
      (∑ k, w k • castVec (principalNormals s k)) := by
  rw [← generatedForm1]
  exact ⟨dualSupport_linear_combination _ _ _ hw (principal_normal_support s),
    tight_combination generators1 (principalNormals s) w (cells1 s) (principal_normals_tight s)⟩

theorem cells2_supported (w : Fin 10 → ℝ) (hw : ∀ k, 0 ≤ w k) (s : Fin 24) :
    SupportsSimplex (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) (cells2 s)
      (secondaryVertex c2VertexCoefficients w (cellVertexIndex2 s)) := by
  refine ⟨c2_vertex_support w hw _, ?_⟩
  have h := tight_combination generators2 (c2VertexCoefficients (cellVertexIndex2 s))
    w (cells2 s) (cells2_tight s)
  simpa only [generatedForm2, secondaryVertex] using h

theorem cells3_supported (w : Fin 10 → ℝ) (hw : ∀ k, 0 ≤ w k) (s : Fin 24) :
    SupportsSimplex (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) (cells3 s)
      (secondaryVertex c3VertexCoefficients w (cellVertexIndex3 s)) := by
  refine ⟨c3_vertex_support w hw _, ?_⟩
  have h := tight_combination generators3 (c3VertexCoefficients (cellVertexIndex3 s))
    w (cells3 s) (cells3_tight s)
  simpa only [generatedForm3, secondaryVertex] using h

theorem cells1_delaunay (w : Fin 10 → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hQ : (principalForm w).PosDef) (s : Fin 24) :
    IsDelaunaySimplex (principalForm w) (cells1 s) :=
  supportsSimplex_isDelaunay hQ _ _ (cells1_supported w hw s)

theorem cells2_delaunay (w : Fin 10 → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hQ : (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).PosDef) (s : Fin 24) :
    IsDelaunaySimplex (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) (cells2 s) :=
  supportsSimplex_isDelaunay hQ _ _ (cells2_supported w hw s)

theorem cells3_delaunay (w : Fin 10 → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hQ : (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)).PosDef) (s : Fin 24) :
    IsDelaunaySimplex (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) (cells3 s) :=
  supportsSimplex_isDelaunay hQ _ _ (cells3_supported w hw s)

end D4.Delaunay
