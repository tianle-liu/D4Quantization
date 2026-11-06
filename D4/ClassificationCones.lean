import D4.ClassificationDefs

/-! Exact nonnegative generator decompositions for reduced superbases. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace D4.Classification
open Matrix Analytic

theorem superInner_symmetric {Q : RealGram} (hQ : Q.IsSymm) (i j : Fin 5) :
    superInner Q i j = superInner Q j i := by
  unfold superInner
  rw [dotProduct_mulVec, ← mulVec_transpose, hQ.eq, dotProduct_comm]

def principalWeights (Q : RealGram) : Fin 10 → ℝ :=
  ![-superInner Q 0 1, -superInner Q 0 2, -superInner Q 0 3, -superInner Q 0 4,
    -superInner Q 1 2, -superInner Q 1 3, -superInner Q 1 4,
    -superInner Q 2 3, -superInner Q 2 4, -superInner Q 3 4]

def secondary2Weights (Q : RealGram) : Fin 9 → ℝ :=
  ![-superInner Q 0 1 - superInner Q 1 2, -superInner Q 0 2 - superInner Q 1 2,
    -superInner Q 0 3, -superInner Q 0 4,
    -superInner Q 1 3 - superInner Q 1 2, -superInner Q 1 4 - superInner Q 1 2,
    -superInner Q 2 3 - superInner Q 1 2, -superInner Q 2 4 - superInner Q 1 2,
    -superInner Q 3 4]

def secondary3Weights (Q : RealGram) : Fin 9 → ℝ :=
  ![-superInner Q 0 1 - superInner Q 1 2 + superInner Q 3 4,
    -superInner Q 0 2 - superInner Q 1 2 + superInner Q 3 4,
    -superInner Q 0 3, -superInner Q 0 4,
    -superInner Q 1 3 - superInner Q 1 2, -superInner Q 1 4 - superInner Q 1 2,
    -superInner Q 2 3 - superInner Q 1 2, -superInner Q 2 4 - superInner Q 1 2,
    superInner Q 3 4]

theorem principal_reconstruction {Q : RealGram} (hQ : Q.IsSymm) :
    Q = principalForm (principalWeights Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [principalForm, principalWeights, rankOne, cone1Vectors, superInner,
      superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      hQ.apply 0 1, hQ.apply 0 2, hQ.apply 0 3, hQ.apply 1 2,
      hQ.apply 1 3, hQ.apply 2 3] <;> ring

theorem secondary2_reconstruction {Q : RealGram} (hQ : Q.IsSymm) :
    Q = secondaryForm cone2Vectors (superInner Q 1 2) (secondary2Weights Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secondaryForm, secondary2Weights, rankOne, cone2Vectors, gramMatrix, superInner,
      superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      hQ.apply 0 1, hQ.apply 0 2, hQ.apply 0 3, hQ.apply 1 2,
      hQ.apply 1 3, hQ.apply 2 3] <;> ring

theorem secondary3_reconstruction {Q : RealGram} (hQ : Q.IsSymm) :
    Q = secondaryForm cone3Vectors (superInner Q 1 2 - superInner Q 3 4)
      (secondary3Weights Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secondaryForm, secondary3Weights, rankOne, cone3Vectors, gramMatrix, superInner,
      superVector, castVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      hQ.apply 0 1, hQ.apply 0 2, hQ.apply 0 3, hQ.apply 1 2,
      hQ.apply 1 3, hQ.apply 2 3] <;> ring

theorem inPrincipalCone_of_superInner_nonpos {Q : RealGram} (hQ : Q.IsSymm)
    (h : ∀ i j : Fin 5, i ≠ j → superInner Q i j ≤ 0) : InPrincipalCone Q := by
  refine ⟨principalWeights Q, ?_, principal_reconstruction hQ⟩
  intro i
  fin_cases i <;> dsimp [principalWeights] <;>
    exact neg_nonneg.mpr (h _ _ (by decide))

theorem inSecondary2_of_pairReduced {Q : RealGram} (hQ : Q.IsSymm) (hr : PairReduced Q)
    (hp : 0 ≤ superInner Q 1 2) (h03 : superInner Q 0 3 ≤ 0)
    (h04 : superInner Q 0 4 ≤ 0) (h34 : superInner Q 3 4 ≤ 0) :
    InSecondaryCone cone2Vectors Q := by
  have h10 := hr 1 0 2 (by decide) (by decide) (by decide)
  have h20 := hr 2 0 1 (by decide) (by decide) (by decide)
  have h13 := hr 1 3 2 (by decide) (by decide) (by decide)
  have h14 := hr 1 4 2 (by decide) (by decide) (by decide)
  have h23 := hr 2 3 1 (by decide) (by decide) (by decide)
  have h24 := hr 2 4 1 (by decide) (by decide) (by decide)
  rw [superInner_symmetric hQ 1 0] at h10
  rw [superInner_symmetric hQ 2 0, superInner_symmetric hQ 2 1] at h20
  rw [superInner_symmetric hQ 2 1] at h23 h24
  refine ⟨superInner Q 1 2, secondary2Weights Q, hp, ?_, secondary2_reconstruction hQ⟩
  intro i
  fin_cases i <;> dsimp [secondary2Weights] <;>
    linarith only [h10, h20, h13, h14, h23, h24, h03, h04, h34]

theorem inSecondary3_of_pairReduced {Q : RealGram} (hQ : Q.IsSymm) (hr : PairReduced Q)
    (hq : 0 ≤ superInner Q 3 4) (hpq : superInner Q 3 4 ≤ superInner Q 1 2) :
    InSecondaryCone cone3Vectors Q := by
  have h10 := hr 1 0 2 (by decide) (by decide) (by decide)
  have h20 := hr 2 0 1 (by decide) (by decide) (by decide)
  have h13 := hr 1 3 2 (by decide) (by decide) (by decide)
  have h14 := hr 1 4 2 (by decide) (by decide) (by decide)
  have h23 := hr 2 3 1 (by decide) (by decide) (by decide)
  have h24 := hr 2 4 1 (by decide) (by decide) (by decide)
  have h30 := hr 3 0 4 (by decide) (by decide) (by decide)
  have h40 := hr 4 0 3 (by decide) (by decide) (by decide)
  rw [superInner_symmetric hQ 1 0] at h10
  rw [superInner_symmetric hQ 2 0, superInner_symmetric hQ 2 1] at h20
  rw [superInner_symmetric hQ 2 1] at h23 h24
  rw [superInner_symmetric hQ 3 0] at h30
  rw [superInner_symmetric hQ 4 0, superInner_symmetric hQ 4 3] at h40
  refine ⟨superInner Q 1 2 - superInner Q 3 4, secondary3Weights Q,
    sub_nonneg.mpr hpq, ?_, secondary3_reconstruction hQ⟩
  intro i
  fin_cases i <;> dsimp [secondary3Weights] <;>
    linarith only [h10, h20, h13, h14, h23, h24, h30, h40, hq]

end D4.Classification
