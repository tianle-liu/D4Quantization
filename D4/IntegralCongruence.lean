import D4.MomentBasisChange

/-! Integer congruence is an equivalence relation, proved using actual
unimodular matrices and their integer inverses. -/
noncomputable section
namespace D4
open Matrix Analytic

theorem realMatrix_one : realMatrix (1 : IntegerMatrix) = 1 := by
  ext i j
  simp [realMatrix, Matrix.one_apply]

theorem realMatrix_mul (U V : IntegerMatrix) : realMatrix (U * V) = realMatrix U * realMatrix V := by
  ext i j
  simp [realMatrix, Matrix.mul_apply]

theorem IntegralCongruent.refl (Q : RealGram) : IntegralCongruent Q Q := by
  refine ⟨1, by simp, ?_⟩
  simp [realMatrix_one]

theorem IntegralCongruent.symm {Q R : RealGram} (h : IntegralCongruent Q R) :
    IntegralCongruent R Q := by
  obtain ⟨U, hU, rfl⟩ := h
  refine ⟨U⁻¹, U.isUnit_nonsing_inv_det hU, ?_⟩
  have hm : realMatrix U * realMatrix U⁻¹ = 1 := by
    rw [← realMatrix_mul, Matrix.mul_nonsing_inv U hU, realMatrix_one]
  calc
    Q = (realMatrix U * realMatrix U⁻¹).transpose * Q *
        (realMatrix U * realMatrix U⁻¹) := by rw [hm]; simp
    _ = _ := by rw [Matrix.transpose_mul]; noncomm_ring

theorem IntegralCongruent.trans {Q R S : RealGram}
    (hQR : IntegralCongruent Q R) (hRS : IntegralCongruent R S) : IntegralCongruent Q S := by
  obtain ⟨U, hU, rfl⟩ := hQR
  obtain ⟨V, hV, rfl⟩ := hRS
  refine ⟨U * V, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact hU.mul hV
  · rw [realMatrix_mul, Matrix.transpose_mul]
    noncomm_ring

theorem IntegralCongruent.posDef {Q R : RealGram} (h : IntegralCongruent Q R)
    (hQ : Q.PosDef) : R.PosDef := by
  obtain ⟨U, hU, rfl⟩ := h
  exact posDef_unimodular_congruence hQ U hU

theorem similarD4Gram_of_ray_congruent {Q : RealGram} (c : ℝ) (hc : 0 < c)
    (h : IntegralCongruent Q (c • gramMatrix ℝ)) : SimilarD4Gram Q :=
  ⟨c, hc, h.symm⟩

theorem normalizedMoment_similarD4 {Q : RealGram} (h : SimilarD4Gram Q) :
    normalizedMoment Q = normalizedMoment (gramMatrix ℝ) := by
  obtain ⟨c, hc, h⟩ := h
  rw [normalizedMoment_integralCongruent h]
  exact normalizedMoment_smul gramMatrix_posDef hc

end D4
