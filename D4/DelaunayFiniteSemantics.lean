import D4.DelaunayC1Checks

import D4.DelaunayC2Checks

import D4.DelaunayC3Checks

import D4.DelaunayLiftingTable

import D4.DelaunayAffine

import D4.DelaunayMatrices

noncomputable section

namespace D4.Delaunay

open Matrix Analytic

theorem singleLifting_eval (w : Fin 10 → ℝ) (j : Fin 10) :
    (∑ k, w k*(singleLifting j k:ℝ))=2*w j := by
  classical
  simp [singleLifting,mul_comm]

theorem doubleLifting_eval (w : Fin 10 → ℝ) (j : Fin 9) :
    (∑ k, w k*(doubleLifting j k:ℝ))=2*(w 0+w j.succ) := by
  simp only [doubleLifting,Pi.add_apply,Int.cast_add,mul_add,Finset.sum_add_distrib,
    singleLifting_eval]


theorem cells1_unimodular (s : Fin 24) :
    (simplexMatrixZ (cells1 s)).det=1 ∨ (simplexMatrixZ (cells1 s)).det = -1 :=
  of_decide_eq_true (List.all_eq_true.mp unimodular1_check s (List.mem_finRange s))

theorem facets1_complete : (facetOccurrences facets1).Nodup ∧
    (facetOccurrences facets1).toFinset=Finset.univ := of_decide_eq_true occurrences1_check

theorem facets1_valid (i : Fin 60) : facetCheck cells1 generators1 (facets1 i)=true :=
  List.all_eq_true.mp all_facets1_check i (List.mem_finRange i)

theorem facets1_geometry (i : Fin 60) :
    (facets1 i).left ≠ (facets1 i).right ∧
    facetVertices (shiftedLeft cells1 (facets1 i)) (facets1 i).leftFace=
      facetVertices (shiftedRight cells1 (facets1 i)) (facets1 i).rightFace ∧
    (∑ j, (facets1 i).barycentric j)=1 ∧
    (∑ j, (facets1 i).barycentric j • shiftedLeft cells1 (facets1 i) j)=
      shiftedRight cells1 (facets1 i) (facets1 i).rightFace ∧
    (facets1 i).barycentric (facets1 i).leftFace = -1 :=
  facetCheck_geometry cells1 generators1 (facets1 i) (facets1_valid i)


theorem facets1_interpolant_lifting (w : Fin 10 → ℝ) (i : Fin 60)
    (L : Vec →ᵃ[ℝ] ℝ)
    (hL : ∀ j, L (castVec (shiftedLeft cells1 (facets1 i) j))=
      quadratic (principalForm w) (castVec (shiftedLeft cells1 (facets1 i) j))) :
    quadratic (principalForm w)
        (castVec (shiftedRight cells1 (facets1 i) (facets1 i).rightFace))-
      L (castVec (shiftedRight cells1 (facets1 i) (facets1 i).rightFace))=
      ∑ k, w k*((facets1 i).lifting k:ℝ) := by
  simpa only [generatedForm1] using liftingDifference_affine cells1 generators1
    (facets1 i) (facets1_valid i) w L (by simpa only [generatedForm1] using hL)


theorem facets1_positive (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (i : Fin 60) :
    0 < liftingDifference generators1 w cells1 (facets1 i) := by
  rw [liftingDifference_eq _ _ _ _ (facets1_valid i)]
  obtain ⟨j,hj⟩ := lifting1_classification i
  rw [hj,singleLifting_eval]
  exact mul_pos (by norm_num) (hw j)


theorem cells2_unimodular (s : Fin 24) :
    (simplexMatrixZ (cells2 s)).det=1 ∨ (simplexMatrixZ (cells2 s)).det = -1 :=
  of_decide_eq_true (List.all_eq_true.mp unimodular2_check s (List.mem_finRange s))

theorem facets2_complete : (facetOccurrences facets2).Nodup ∧
    (facetOccurrences facets2).toFinset=Finset.univ := of_decide_eq_true occurrences2_check

theorem facets2_valid (i : Fin 60) : facetCheck cells2 generators2 (facets2 i)=true :=
  List.all_eq_true.mp all_facets2_check i (List.mem_finRange i)

theorem facets2_geometry (i : Fin 60) :
    (facets2 i).left ≠ (facets2 i).right ∧
    facetVertices (shiftedLeft cells2 (facets2 i)) (facets2 i).leftFace=
      facetVertices (shiftedRight cells2 (facets2 i)) (facets2 i).rightFace ∧
    (∑ j, (facets2 i).barycentric j)=1 ∧
    (∑ j, (facets2 i).barycentric j • shiftedLeft cells2 (facets2 i) j)=
      shiftedRight cells2 (facets2 i) (facets2 i).rightFace ∧
    (facets2 i).barycentric (facets2 i).leftFace = -1 :=
  facetCheck_geometry cells2 generators2 (facets2 i) (facets2_valid i)


theorem facets2_interpolant_lifting (w : Fin 10 → ℝ) (i : Fin 60)
    (L : Vec →ᵃ[ℝ] ℝ)
    (hL : ∀ j, L (castVec (shiftedLeft cells2 (facets2 i) j))=
      quadratic (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) (castVec (shiftedLeft cells2 (facets2 i) j))) :
    quadratic (secondaryForm cone2Vectors (w 0) (fun j => w j.succ))
        (castVec (shiftedRight cells2 (facets2 i) (facets2 i).rightFace))-
      L (castVec (shiftedRight cells2 (facets2 i) (facets2 i).rightFace))=
      ∑ k, w k*((facets2 i).lifting k:ℝ) := by
  simpa only [generatedForm2] using liftingDifference_affine cells2 generators2
    (facets2 i) (facets2_valid i) w L (by simpa only [generatedForm2] using hL)


theorem facets2_positive (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (i : Fin 60) :
    0 < liftingDifference generators2 w cells2 (facets2 i) := by
  rw [liftingDifference_eq _ _ _ _ (facets2_valid i)]
  rcases lifting2_classification i with h | ⟨j,h⟩ | ⟨j,h⟩
  · rw [h,singleLifting_eval]
    exact mul_pos (by norm_num) (hw 0)
  · rw [h,singleLifting_eval]
    exact mul_pos (by norm_num) (hw j.succ)
  · rw [h,doubleLifting_eval]
    exact mul_pos (by norm_num) (add_pos (hw 0) (hw j.succ))


theorem cells3_unimodular (s : Fin 24) :
    (simplexMatrixZ (cells3 s)).det=1 ∨ (simplexMatrixZ (cells3 s)).det = -1 :=
  of_decide_eq_true (List.all_eq_true.mp unimodular3_check s (List.mem_finRange s))

theorem facets3_complete : (facetOccurrences facets3).Nodup ∧
    (facetOccurrences facets3).toFinset=Finset.univ := of_decide_eq_true occurrences3_check

theorem facets3_valid (i : Fin 60) : facetCheck cells3 generators3 (facets3 i)=true :=
  List.all_eq_true.mp all_facets3_check i (List.mem_finRange i)

theorem facets3_geometry (i : Fin 60) :
    (facets3 i).left ≠ (facets3 i).right ∧
    facetVertices (shiftedLeft cells3 (facets3 i)) (facets3 i).leftFace=
      facetVertices (shiftedRight cells3 (facets3 i)) (facets3 i).rightFace ∧
    (∑ j, (facets3 i).barycentric j)=1 ∧
    (∑ j, (facets3 i).barycentric j • shiftedLeft cells3 (facets3 i) j)=
      shiftedRight cells3 (facets3 i) (facets3 i).rightFace ∧
    (facets3 i).barycentric (facets3 i).leftFace = -1 :=
  facetCheck_geometry cells3 generators3 (facets3 i) (facets3_valid i)


theorem facets3_interpolant_lifting (w : Fin 10 → ℝ) (i : Fin 60)
    (L : Vec →ᵃ[ℝ] ℝ)
    (hL : ∀ j, L (castVec (shiftedLeft cells3 (facets3 i) j))=
      quadratic (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) (castVec (shiftedLeft cells3 (facets3 i) j))) :
    quadratic (secondaryForm cone3Vectors (w 0) (fun j => w j.succ))
        (castVec (shiftedRight cells3 (facets3 i) (facets3 i).rightFace))-
      L (castVec (shiftedRight cells3 (facets3 i) (facets3 i).rightFace))=
      ∑ k, w k*((facets3 i).lifting k:ℝ) := by
  simpa only [generatedForm3] using liftingDifference_affine cells3 generators3
    (facets3 i) (facets3_valid i) w L (by simpa only [generatedForm3] using hL)


theorem facets3_positive (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (i : Fin 60) :
    0 < liftingDifference generators3 w cells3 (facets3 i) := by
  rw [liftingDifference_eq _ _ _ _ (facets3_valid i)]
  rcases lifting3_classification i with h | ⟨j,h⟩ | ⟨j,h⟩
  · rw [h,singleLifting_eval]
    exact mul_pos (by norm_num) (hw 0)
  · rw [h,singleLifting_eval]
    exact mul_pos (by norm_num) (hw j.succ)
  · rw [h,doubleLifting_eval]
    exact mul_pos (by norm_num) (add_pos (hw 0) (hw j.succ))


end D4.Delaunay
