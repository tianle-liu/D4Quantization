import D4.ClassificationCones
import D4.PrincipalSecondaryBoundary
import D4.DelaunayMatrices

/-! Explicit inverse coordinates in the entire ten-dimensional space of
 symmetric four by four matrices. -/
noncomputable section
set_option maxHeartbeats 600000
namespace D4.Delaunay
open Analytic Classification Principal Matrix

def coneForm (i : Fin 3) (w : Fin 10 → ℝ) : Gram :=
  ![principalForm w, secondaryForm cone2Vectors (w 0) (fun k => w k.succ),
    secondaryForm cone3Vectors (w 0) (fun k => w k.succ)] i

def coneCoordinates (i : Fin 3) (Q : Gram) : Fin 10 → ℝ :=
  ![principalWeights Q, Fin.cons (superInner Q 1 2) (secondary2Weights Q),
    Fin.cons (superInner Q 1 2-superInner Q 3 4) (secondary3Weights Q)] i

theorem coneForm_coordinates (i : Fin 3) (Q : Gram) (hQ : Q.IsSymm) :
    coneForm i (coneCoordinates i Q)=Q := by
  fin_cases i
  · exact (principal_reconstruction hQ).symm
  · exact (secondary2_reconstruction hQ).symm
  · exact (secondary3_reconstruction hQ).symm

def coordinateFormula (i : Fin 3) (Q : Gram) : Fin 10 → ℝ :=
  ![![(Q 0 0+Q 1 0+Q 2 0+Q 3 0),(Q 0 1+Q 1 1+Q 2 1+Q 3 1),(Q 0 2+Q 1 2+Q 2 2+Q 3 2),(Q 0 3+Q 1 3+Q 2 3+Q 3 3),-Q 0 1,-Q 0 2,-Q 0 3,-Q 1 2,-Q 1 3,-Q 2 3],
    ![Q 0 1,(Q 0 0+Q 1 0+Q 2 0+Q 3 0)-Q 0 1,(Q 0 1+Q 1 1+Q 2 1+Q 3 1)-Q 0 1,(Q 0 2+Q 1 2+Q 2 2+Q 3 2),(Q 0 3+Q 1 3+Q 2 3+Q 3 3),-Q 0 2-Q 0 1,-Q 0 3-Q 0 1,-Q 1 2-Q 0 1,-Q 1 3-Q 0 1,-Q 2 3],
    ![Q 0 1-Q 2 3,(Q 0 0+Q 1 0+Q 2 0+Q 3 0)-Q 0 1+Q 2 3,(Q 0 1+Q 1 1+Q 2 1+Q 3 1)-Q 0 1+Q 2 3,(Q 0 2+Q 1 2+Q 2 2+Q 3 2),(Q 0 3+Q 1 3+Q 2 3+Q 3 3),-Q 0 2-Q 0 1,-Q 0 3-Q 0 1,-Q 1 2-Q 0 1,-Q 1 3-Q 0 1,Q 2 3]] i

theorem coneCoordinates_eq_formula (i : Fin 3) (Q : Gram) :
    coneCoordinates i Q=coordinateFormula i Q := by
  ext k
  fin_cases i <;> fin_cases k
  · change -superInner Q 0 1 = (Q 0 0+Q 1 0+Q 2 0+Q 3 0)
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 0 2 = (Q 0 1+Q 1 1+Q 2 1+Q 3 1)
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 0 3 = (Q 0 2+Q 1 2+Q 2 2+Q 3 2)
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 0 4 = (Q 0 3+Q 1 3+Q 2 3+Q 3 3)
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 1 2 = -Q 0 1
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 1 3 = -Q 0 2
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 1 4 = -Q 0 3
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 2 3 = -Q 1 2
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 2 4 = -Q 1 3
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 3 4 = -Q 2 3
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change superInner Q 1 2 = Q 0 1
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 0 1-superInner Q 1 2 = (Q 0 0+Q 1 0+Q 2 0+Q 3 0)-Q 0 1
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 0 2-superInner Q 1 2 = (Q 0 1+Q 1 1+Q 2 1+Q 3 1)-Q 0 1
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 0 3 = (Q 0 2+Q 1 2+Q 2 2+Q 3 2)
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 0 4 = (Q 0 3+Q 1 3+Q 2 3+Q 3 3)
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 1 3-superInner Q 1 2 = -Q 0 2-Q 0 1
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 1 4-superInner Q 1 2 = -Q 0 3-Q 0 1
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 2 3-superInner Q 1 2 = -Q 1 2-Q 0 1
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 2 4-superInner Q 1 2 = -Q 1 3-Q 0 1
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 3 4 = -Q 2 3
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change superInner Q 1 2-superInner Q 3 4 = Q 0 1-Q 2 3
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 0 1-superInner Q 1 2+superInner Q 3 4 = (Q 0 0+Q 1 0+Q 2 0+Q 3 0)-Q 0 1+Q 2 3
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 0 2-superInner Q 1 2+superInner Q 3 4 = (Q 0 1+Q 1 1+Q 2 1+Q 3 1)-Q 0 1+Q 2 3
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 0 3 = (Q 0 2+Q 1 2+Q 2 2+Q 3 2)
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 0 4 = (Q 0 3+Q 1 3+Q 2 3+Q 3 3)
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 1 3-superInner Q 1 2 = -Q 0 2-Q 0 1
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 1 4-superInner Q 1 2 = -Q 0 3-Q 0 1
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 2 3-superInner Q 1 2 = -Q 1 2-Q 0 1
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change -superInner Q 2 4-superInner Q 1 2 = -Q 1 3-Q 0 1
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · change superInner Q 3 4 = Q 2 3
    simp [superInner, superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring

theorem coneCoordinates_form (i : Fin 3) (w : Fin 10 → ℝ) :
    coneCoordinates i (coneForm i w)=w := by
  rw [coneCoordinates_eq_formula]
  ext k
  fin_cases i <;> fin_cases k
  · change ((principalForm w) 0 0+(principalForm w) 1 0+(principalForm w) 2 0+(principalForm w) 3 0) = w 0
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change ((principalForm w) 0 1+(principalForm w) 1 1+(principalForm w) 2 1+(principalForm w) 3 1) = w 1
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change ((principalForm w) 0 2+(principalForm w) 1 2+(principalForm w) 2 2+(principalForm w) 3 2) = w 2
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change ((principalForm w) 0 3+(principalForm w) 1 3+(principalForm w) 2 3+(principalForm w) 3 3) = w 3
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(principalForm w) 0 1 = w 4
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(principalForm w) 0 2 = w 5
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(principalForm w) 0 3 = w 6
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(principalForm w) 1 2 = w 7
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(principalForm w) 1 3 = w 8
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(principalForm w) 2 3 = w 9
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 0 1 = w 0
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change ((secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 0 0+(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 1 0+(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 2 0+(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 3 0)-(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 0 1 = w 1
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change ((secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 0 1+(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 1 1+(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 2 1+(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 3 1)-(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 0 1 = w 2
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change ((secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 0 2+(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 1 2+(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 2 2+(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 3 2) = w 3
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change ((secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 0 3+(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 1 3+(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 2 3+(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 3 3) = w 4
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 0 2-(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 0 1 = w 5
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 0 3-(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 0 1 = w 6
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 1 2-(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 0 1 = w 7
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 1 3-(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 0 1 = w 8
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) 2 3 = w 9
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 0 1-(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 2 3 = w 0
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change ((secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 0 0+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 1 0+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 2 0+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 3 0)-(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 0 1+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 2 3 = w 1
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change ((secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 0 1+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 1 1+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 2 1+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 3 1)-(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 0 1+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 2 3 = w 2
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change ((secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 0 2+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 1 2+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 2 2+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 3 2) = w 3
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change ((secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 0 3+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 1 3+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 2 3+(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 3 3) = w 4
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 0 2-(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 0 1 = w 5
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 0 3-(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 0 1 = w 6
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 1 2-(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 0 1 = w 7
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change -(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 1 3-(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 0 1 = w 8
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring
  · change (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) 2 3 = w 9
    simp [principalForm, secondaryForm, rankOne, cone1Vectors, cone2Vectors, cone3Vectors, gramMatrix, Fin.sum_univ_succ]
    <;> ring

theorem coneForm_injective (i : Fin 3) : Function.Injective (coneForm i) :=
  Function.LeftInverse.injective (coneCoordinates_form i)

theorem coneForm_isSymm (i : Fin 3) (w : Fin 10 → ℝ) : (coneForm i w).IsSymm := by
  fin_cases i
  · exact by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using principal_isHermitian w
  · exact by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using secondary_isHermitian _ _ _
  · exact by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using secondary_isHermitian _ _ _

theorem coneForm_posDef (i : Fin 3) (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    (coneForm i w).PosDef := by
  fin_cases i
  · exact Principal.principal_posDef_of_pos hw
  · exact Principal.secondary_posDef_of_pos _ (hw 0) (fun k => (hw k.succ).le)
  · exact Principal.secondary_posDef_of_pos _ (hw 0) (fun k => (hw k.succ).le)

theorem coneForm_continuous (i : Fin 3) : Continuous (coneForm i) := by
  fin_cases i
  · change Continuous (fun w : Fin 10 → ℝ => principalForm w)
    unfold principalForm
    fun_prop
  · change Continuous (fun w : Fin 10 → ℝ => secondaryForm cone2Vectors (w 0) (fun k => w k.succ))
    unfold secondaryForm
    fun_prop
  · change Continuous (fun w : Fin 10 → ℝ => secondaryForm cone3Vectors (w 0) (fun k => w k.succ))
    unfold secondaryForm
    fun_prop

theorem coneCoordinates_continuous (i : Fin 3) : Continuous (coneCoordinates i) := by
  have he : coneCoordinates i=coordinateFormula i := funext (coneCoordinates_eq_formula i)
  rw [he]
  apply continuous_pi
  intro k
  fin_cases i <;> fin_cases k
  · change Continuous (fun Q : Gram => (Q 0 0+Q 1 0+Q 2 0+Q 3 0))
    fun_prop
  · change Continuous (fun Q : Gram => (Q 0 1+Q 1 1+Q 2 1+Q 3 1))
    fun_prop
  · change Continuous (fun Q : Gram => (Q 0 2+Q 1 2+Q 2 2+Q 3 2))
    fun_prop
  · change Continuous (fun Q : Gram => (Q 0 3+Q 1 3+Q 2 3+Q 3 3))
    fun_prop
  · change Continuous (fun Q : Gram => -Q 0 1)
    fun_prop
  · change Continuous (fun Q : Gram => -Q 0 2)
    fun_prop
  · change Continuous (fun Q : Gram => -Q 0 3)
    fun_prop
  · change Continuous (fun Q : Gram => -Q 1 2)
    fun_prop
  · change Continuous (fun Q : Gram => -Q 1 3)
    fun_prop
  · change Continuous (fun Q : Gram => -Q 2 3)
    fun_prop
  · change Continuous (fun Q : Gram => Q 0 1)
    fun_prop
  · change Continuous (fun Q : Gram => (Q 0 0+Q 1 0+Q 2 0+Q 3 0)-Q 0 1)
    fun_prop
  · change Continuous (fun Q : Gram => (Q 0 1+Q 1 1+Q 2 1+Q 3 1)-Q 0 1)
    fun_prop
  · change Continuous (fun Q : Gram => (Q 0 2+Q 1 2+Q 2 2+Q 3 2))
    fun_prop
  · change Continuous (fun Q : Gram => (Q 0 3+Q 1 3+Q 2 3+Q 3 3))
    fun_prop
  · change Continuous (fun Q : Gram => -Q 0 2-Q 0 1)
    fun_prop
  · change Continuous (fun Q : Gram => -Q 0 3-Q 0 1)
    fun_prop
  · change Continuous (fun Q : Gram => -Q 1 2-Q 0 1)
    fun_prop
  · change Continuous (fun Q : Gram => -Q 1 3-Q 0 1)
    fun_prop
  · change Continuous (fun Q : Gram => -Q 2 3)
    fun_prop
  · change Continuous (fun Q : Gram => Q 0 1-Q 2 3)
    fun_prop
  · change Continuous (fun Q : Gram => (Q 0 0+Q 1 0+Q 2 0+Q 3 0)-Q 0 1+Q 2 3)
    fun_prop
  · change Continuous (fun Q : Gram => (Q 0 1+Q 1 1+Q 2 1+Q 3 1)-Q 0 1+Q 2 3)
    fun_prop
  · change Continuous (fun Q : Gram => (Q 0 2+Q 1 2+Q 2 2+Q 3 2))
    fun_prop
  · change Continuous (fun Q : Gram => (Q 0 3+Q 1 3+Q 2 3+Q 3 3))
    fun_prop
  · change Continuous (fun Q : Gram => -Q 0 2-Q 0 1)
    fun_prop
  · change Continuous (fun Q : Gram => -Q 0 3-Q 0 1)
    fun_prop
  · change Continuous (fun Q : Gram => -Q 1 2-Q 0 1)
    fun_prop
  · change Continuous (fun Q : Gram => -Q 1 3-Q 0 1)
    fun_prop
  · change Continuous (fun Q : Gram => Q 2 3)
    fun_prop


end D4.Delaunay
