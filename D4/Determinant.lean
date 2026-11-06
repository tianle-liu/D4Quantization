import D4.Targets
import Mathlib.Tactic.Positivity

/-!
# Determinant and trace bounds in dimension four

The bound is proved for actual positive-definite real matrices by applying
an exact four-variable arithmetic--geometric mean identity to their
eigenvalues. The equality case is transported back through the spectral
theorem. No geometric classification or moment formula is assumed here.
-/

namespace D4

open scoped Matrix

private theorem amgm_four (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a*b*c*d ≤ ((a+b+c+d)/4)^4 := by
  have h₁ : 0 ≤ (a+b-c-d)^2 * ((a+b)^2 + 6*(a+b)*(c+d) + (c+d)^2) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have h₂ : 0 ≤ 16*(a-b)^2*(c+d)^2 := by positivity
  have h₃ : 0 ≤ 64*a*b*(c-d)^2 := by positivity
  apply sub_nonneg.mp
  have hid : ((a+b+c+d)/4)^4 - a*b*c*d =
      ((a+b-c-d)^2 * ((a+b)^2 + 6*(a+b)*(c+d) + (c+d)^2) +
       16*(a-b)^2*(c+d)^2 + 64*a*b*(c-d)^2) / 256 := by ring
  rw [hid]
  exact div_nonneg (add_nonneg (add_nonneg h₁ h₂) h₃) (by norm_num)

private theorem amgm_four_eq (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d)
    (he : a*b*c*d = ((a+b+c+d)/4)^4) : a = b ∧ a = c ∧ a = d := by
  have hcoef : 0 < (a+b)^2 + 6*(a+b)*(c+d) + (c+d)^2 := by positivity
  have h₁ : 0 ≤ (a+b-c-d)^2 * ((a+b)^2 + 6*(a+b)*(c+d) + (c+d)^2) :=
    mul_nonneg (sq_nonneg _) hcoef.le
  have h₂ : 0 ≤ 16*(a-b)^2*(c+d)^2 := by positivity
  have h₃ : 0 ≤ 64*a*b*(c-d)^2 := by positivity
  have hs : (a+b-c-d)^2 * ((a+b)^2 + 6*(a+b)*(c+d) + (c+d)^2) +
      16*(a-b)^2*(c+d)^2 + 64*a*b*(c-d)^2 = 0 := by
    calc
      _ = 256 * (((a+b+c+d)/4)^4 - a*b*c*d) := by ring
      _ = 0 := by rw [← he]; ring
  have hz₁ : (a+b-c-d)^2 * ((a+b)^2 + 6*(a+b)*(c+d) + (c+d)^2) = 0 := by
    linarith only [hs, h₁, h₂, h₃]
  have hz₂ : 16*(a-b)^2*(c+d)^2 = 0 := by
    linarith only [hs, h₁, h₂, h₃]
  have hz₃ : 64*a*b*(c-d)^2 = 0 := by
    linarith only [hs, h₁, h₂, h₃]
  have hsum : a+b-c-d = 0 := by
    have := (mul_eq_zero.mp hz₁).resolve_right (ne_of_gt hcoef)
    exact pow_eq_zero this
  have hab : a-b = 0 := by
    have hcd : (c+d)^2 ≠ 0 := ne_of_gt (by positivity)
    have := (mul_eq_zero.mp hz₂).resolve_right hcd
    have := (mul_eq_zero.mp this).resolve_left (by norm_num)
    exact pow_eq_zero this
  have hcd : c-d = 0 := by
    have hp : (64:ℝ)*a*b ≠ 0 := ne_of_gt (by positivity)
    exact pow_eq_zero ((mul_eq_zero.mp hz₃).resolve_left hp)
  constructor
  · linarith
  constructor <;> linarith

/-- Trace is the sum of the eigenvalues, stated for real symmetric matrices. -/
theorem trace_eq_sum_eigenvalues {Q : Matrix (Fin 4) (Fin 4) ℝ}
    (hQ : Q.IsHermitian) : Matrix.trace Q = ∑ i, hQ.eigenvalues i := by
  conv_lhs => rw [hQ.spectral_theorem, Matrix.trace_mul_cycle]
  simp [Matrix.trace, Matrix.diag]

theorem trace_pos {Q : RealGram} (hQ : Q.PosDef) : 0 < Matrix.trace Q := by
  rw [trace_eq_sum_eigenvalues hQ.isHermitian]
  exact Finset.sum_pos' (fun i _ => (hQ.eigenvalues_pos i).le)
    ⟨0, Finset.mem_univ _, hQ.eigenvalues_pos 0⟩

/-- The arithmetic--geometric mean determinant bound in dimension four. -/
theorem det_le_trace_fourth {Q : Matrix (Fin 4) (Fin 4) ℝ} (hQ : Q.PosDef) :
    Q.det ≤ (Matrix.trace Q / 4)^4 := by
  rw [hQ.isHermitian.det_eq_prod_eigenvalues, trace_eq_sum_eigenvalues hQ.isHermitian]
  simpa [Fin.prod_univ_succ, Fin.sum_univ_succ, mul_assoc, add_assoc] using
    amgm_four (hQ.isHermitian.eigenvalues 0) (hQ.isHermitian.eigenvalues 1)
      (hQ.isHermitian.eigenvalues 2) (hQ.isHermitian.eigenvalues 3)
      (hQ.eigenvalues_pos 0).le (hQ.eigenvalues_pos 1).le
      (hQ.eigenvalues_pos 2).le (hQ.eigenvalues_pos 3).le

/-- Equality in the determinant bound forces a scalar matrix. -/
theorem eq_scalar_of_det_eq_trace_fourth {Q : Matrix (Fin 4) (Fin 4) ℝ}
    (hQ : Q.PosDef) (he : Q.det = (Matrix.trace Q / 4)^4) :
    Q = (Matrix.trace Q / 4) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have htr := trace_eq_sum_eigenvalues hQ.isHermitian
  have hprod := hQ.isHermitian.det_eq_prod_eigenvalues
  simp [Fin.prod_univ_succ, Fin.sum_univ_succ] at htr hprod
  have he' : hQ.isHermitian.eigenvalues 0 * hQ.isHermitian.eigenvalues 1 *
      hQ.isHermitian.eigenvalues 2 * hQ.isHermitian.eigenvalues 3 =
      ((hQ.isHermitian.eigenvalues 0 + hQ.isHermitian.eigenvalues 1 +
        hQ.isHermitian.eigenvalues 2 + hQ.isHermitian.eigenvalues 3)/4)^4 := by
    simpa [hprod, htr, mul_assoc, add_assoc] using he
  obtain ⟨hab, hac, had⟩ := amgm_four_eq _ _ _ _
    (hQ.eigenvalues_pos 0) (hQ.eigenvalues_pos 1)
    (hQ.eigenvalues_pos 2) (hQ.eigenvalues_pos 3) he'
  have heigen : ∀ i, hQ.isHermitian.eigenvalues i = Matrix.trace Q / 4 := by
    intro i
    fin_cases i <;> simp only [Fin.reduceFinMk] <;> linarith only [hab, hac, had, htr]
  have hfun : hQ.isHermitian.eigenvalues = fun _ => Matrix.trace Q / 4 := funext heigen
  have hdiag : Matrix.diagonal (fun _ : Fin 4 => Matrix.trace Q / 4) =
      (Matrix.trace Q / 4) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  conv_lhs => rw [hQ.isHermitian.spectral_theorem]
  simp [Function.comp_def, hfun, hdiag, Matrix.mul_smul, Matrix.smul_mul]

/-- Congruence by the inverse of the displayed lattice basis. -/
noncomputable def basisNormalized (Q : RealGram) : RealGram :=
  (basisMatrix ℝ)⁻¹.transpose * Q * (basisMatrix ℝ)⁻¹

private theorem basisMatrix_isUnit : IsUnit (basisMatrix ℝ) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_basisMatrix]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

theorem basisNormalized_posDef {Q : RealGram} (hQ : Q.PosDef) :
    (basisNormalized Q).PosDef := by
  have hi : Function.Injective (basisMatrix ℝ)⁻¹.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (Matrix.isUnit_nonsing_inv_iff.mpr basisMatrix_isUnit)
  simpa [basisNormalized, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hQ.conjTranspose_mul_mul_same hi

theorem det_basisNormalized (Q : RealGram) : (basisNormalized Q).det = Q.det / 4 := by
  simp [basisNormalized, Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv,
    det_basisMatrix, Ring.inverse_eq_inv]
  ring

theorem trace_basisNormalized (Q : RealGram) :
    Matrix.trace (basisNormalized Q) = Matrix.trace ((gramMatrix ℝ)⁻¹ * Q) := by
  have hi : (basisMatrix ℝ)⁻¹ * (basisMatrix ℝ)⁻¹.transpose = (gramMatrix ℝ)⁻¹ := by
    rw [← basisMatrix_transpose_mul, Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv]
  rw [basisNormalized, Matrix.trace_mul_cycle, hi]

theorem basisNormalized_restore (Q : RealGram) :
    (basisMatrix ℝ).transpose * basisNormalized Q * basisMatrix ℝ = Q := by
  have hi : (basisMatrix ℝ)⁻¹ * basisMatrix ℝ = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp basisMatrix_isUnit)
  have ht : (basisMatrix ℝ).transpose * (basisMatrix ℝ)⁻¹.transpose = 1 := by
    simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hi
  simp only [basisNormalized, Matrix.mul_assoc, hi, Matrix.mul_one]
  rw [← Matrix.mul_assoc, ht, Matrix.one_mul]

/-- The determinant bound relative to A; it holds for every positive-definite Q. -/
theorem det_le_gram_relative {Q : RealGram} (hQ : Q.PosDef) :
    Q.det ≤ 4 * (Matrix.trace ((gramMatrix ℝ)⁻¹ * Q) / 4)^4 := by
  have h := det_le_trace_fourth (basisNormalized_posDef hQ)
  rw [det_basisNormalized, trace_basisNormalized] at h
  linarith

/-- The equality ray in the relative determinant inequality. -/
theorem det_eq_gram_relative_iff {Q : RealGram} (hQ : Q.PosDef) :
    Q.det = 4 * (Matrix.trace ((gramMatrix ℝ)⁻¹ * Q) / 4)^4 ↔
    Q = (Matrix.trace ((gramMatrix ℝ)⁻¹ * Q) / 4) • gramMatrix ℝ := by
  constructor
  · intro he
    have he' : (basisNormalized Q).det = (Matrix.trace (basisNormalized Q)/4)^4 := by
      rw [det_basisNormalized, trace_basisNormalized]
      linarith
    have hn := eq_scalar_of_det_eq_trace_fourth (basisNormalized_posDef hQ) he'
    calc
      Q = (basisMatrix ℝ).transpose * basisNormalized Q * basisMatrix ℝ :=
        (basisNormalized_restore Q).symm
      _ = (Matrix.trace ((gramMatrix ℝ)⁻¹ * Q) / 4) • gramMatrix ℝ := by
        rw [hn, trace_basisNormalized]
        simp [Matrix.mul_smul, Matrix.smul_mul, basisMatrix_transpose_mul]
  · intro he
    calc
      Q.det = ((Matrix.trace ((gramMatrix ℝ)⁻¹ * Q) / 4) • gramMatrix ℝ).det :=
        congrArg Matrix.det he
      _ = _ := by simp [Matrix.det_smul, det_gramMatrix, mul_comm]

/-- The article's trace parameter for either secondary cone. -/
noncomputable def secondaryTraceParameter (a : ℝ) (w : Fin 9 → ℝ) : ℝ :=
  a + (∑ i, w i) / 4

theorem trace_secondaryForm {v : Fin 9 → Fin 4 → ℝ}
    (hv : ∀ j, Matrix.trace ((gramMatrix ℝ)⁻¹ * rankOne (v j)) = 1)
    (a : ℝ) (w : Fin 9 → ℝ) :
    Matrix.trace ((gramMatrix ℝ)⁻¹ * secondaryForm v a w) / 4 =
      secondaryTraceParameter a w := by
  have hi : (gramMatrix ℝ)⁻¹ * gramMatrix ℝ = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp gramMatrix_posDef.isUnit)
  simp [secondaryForm, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sum,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum, hi, hv,
    Matrix.trace_one, secondaryTraceParameter]
  ring

theorem secondaryTraceParameter_pos {v : Fin 9 → Fin 4 → ℝ}
    (hv : ∀ j, Matrix.trace ((gramMatrix ℝ)⁻¹ * rankOne (v j)) = 1)
    (a : ℝ) (w : Fin 9 → ℝ) (hQ : (secondaryForm v a w).PosDef) :
    0 < secondaryTraceParameter a w := by
  have ht := trace_pos (basisNormalized_posDef hQ)
  rw [trace_basisNormalized] at ht
  rw [← trace_secondaryForm hv]
  exact div_pos ht (by norm_num)

/-- The C₂ determinant bound, including positive-definite boundary forms. -/
theorem det_secondary2_le (a : ℝ) (w : Fin 9 → ℝ)
    (hQ : (secondaryForm cone2Vectors a w).PosDef) :
    (secondaryForm cone2Vectors a w).det ≤ 4*(secondaryTraceParameter a w)^4 := by
  simpa [trace_secondaryForm cone2_trace_normalization] using det_le_gram_relative hQ

/-- The C₃ determinant bound, including positive-definite boundary forms. -/
theorem det_secondary3_le (a : ℝ) (w : Fin 9 → ℝ)
    (hQ : (secondaryForm cone3Vectors a w).PosDef) :
    (secondaryForm cone3Vectors a w).det ≤ 4*(secondaryTraceParameter a w)^4 := by
  simpa [trace_secondaryForm cone3_trace_normalization] using det_le_gram_relative hQ

theorem det_secondary2_eq_iff (a : ℝ) (w : Fin 9 → ℝ)
    (hQ : (secondaryForm cone2Vectors a w).PosDef) :
    (secondaryForm cone2Vectors a w).det = 4*(secondaryTraceParameter a w)^4 ↔
    secondaryForm cone2Vectors a w = secondaryTraceParameter a w • gramMatrix ℝ := by
  simpa [trace_secondaryForm cone2_trace_normalization] using det_eq_gram_relative_iff hQ

theorem det_secondary3_eq_iff (a : ℝ) (w : Fin 9 → ℝ)
    (hQ : (secondaryForm cone3Vectors a w).PosDef) :
    (secondaryForm cone3Vectors a w).det = 4*(secondaryTraceParameter a w)^4 ↔
    secondaryForm cone3Vectors a w = secondaryTraceParameter a w • gramMatrix ℝ := by
  simpa [trace_secondaryForm cone3_trace_normalization] using det_eq_gram_relative_iff hQ

/-- Relative determinant inequality for any positive-definite reference matrix. -/
theorem det_le_relative {Q H : RealGram} (hQ : Q.PosDef) (hH : H.PosDef) :
    Q.det ≤ H.det * (Matrix.trace (H⁻¹ * Q) / 4)^4 := by
  let C : RealGram := hH.inv.posSemidef.sqrt
  have hcsq : C * C = H⁻¹ := hH.inv.posSemidef.sqrt_mul_self
  have hch : C.conjTranspose = C := hH.inv.posSemidef.posSemidef_sqrt.isHermitian
  have hcu : IsUnit C := isUnit_mul_self_iff.mp (hcsq.symm ▸ hH.inv.isUnit)
  have hc := hQ.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hcu)
  have hd : C.det * C.det = H.det⁻¹ := by
    have hh := congrArg Matrix.det hcsq
    simpa [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using hh
  have hdet : (C.conjTranspose * Q * C).det = Q.det * H.det⁻¹ := by
    rw [hch, Matrix.det_mul, Matrix.det_mul]
    calc
      C.det * Q.det * C.det = Q.det * (C.det * C.det) := by ring
      _ = _ := by rw [hd]
  have htr : Matrix.trace (C.conjTranspose * Q * C) = Matrix.trace (H⁻¹ * Q) := by
    rw [Matrix.trace_mul_cycle, hch, hcsq]
  have hh := det_le_trace_fourth hc
  rw [hdet, htr] at hh
  calc
    Q.det = (Q.det * H.det⁻¹) * H.det := by rw [mul_assoc, inv_mul_cancel₀ hH.det_pos.ne', mul_one]
    _ ≤ (Matrix.trace (H⁻¹ * Q) / 4)^4 * H.det :=
      mul_le_mul_of_nonneg_right hh hH.det_pos.le
    _ = _ := mul_comm _ _

/-- The principal-cone reference matrix, equal to `5I - J`. -/
def principalReference : RealGram :=
  !![4,-1,-1,-1; -1,4,-1,-1; -1,-1,4,-1; -1,-1,-1,4]

theorem principalReference_posDef : principalReference.PosDef := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [principalReference, Matrix.conjTranspose_apply]
  · intro x hx
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hs : 0 < ∑ j : Fin 4, (x j)^2 := by
      apply Finset.sum_pos' (fun j _ => sq_nonneg (x j))
      exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
    simp [Fin.sum_univ_succ] at hs
    simp [principalReference, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    nlinarith only [hs, sq_nonneg (x 0-x 1), sq_nonneg (x 0-x 2),
      sq_nonneg (x 0-x 3), sq_nonneg (x 1-x 2), sq_nonneg (x 1-x 3),
      sq_nonneg (x 2-x 3)]

theorem det_principalReference : principalReference.det = 125 := by
  let H : Matrix (Fin 4) (Fin 4) ℤ :=
    !![4,-1,-1,-1; -1,4,-1,-1; -1,-1,4,-1; -1,-1,-1,4]
  have hdet : H.det = 125 := by decide
  have hmap : H.map (Int.castRingHom ℝ) = principalReference := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [H, principalReference]
  rw [← hmap]
  change (H.map (fun x : ℤ => (x : ℝ))).det = 125
  rw [← Int.cast_det, hdet]
  norm_num

noncomputable def inversePrincipalReference : RealGram :=
  !![2/5,1/5,1/5,1/5; 1/5,2/5,1/5,1/5;
     1/5,1/5,2/5,1/5; 1/5,1/5,1/5,2/5]

theorem principalReference_inv : principalReference⁻¹ = inversePrincipalReference := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, principalReference, inversePrincipalReference]

theorem cone1_trace_normalization (j : Fin 10) :
    Matrix.trace (principalReference⁻¹ * rankOne (cone1Vectors j)) = 2/5 := by
  rw [principalReference_inv]
  fin_cases j <;>
    norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
      inversePrincipalReference, rankOne, cone1Vectors]

/-- The principal-cone determinant bound used in Theorem A. -/
theorem det_principal_le (w : Fin 10 → ℝ) (hQ : (principalForm w).PosDef) :
    (principalForm w).det ≤ (∑ i, w i)^4 / 80 := by
  have ht : Matrix.trace (principalReference⁻¹ * principalForm w) =
      (∑ i, w i) * (2/5) := by
    simp [principalForm, Matrix.mul_sum, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, cone1_trace_normalization, Finset.sum_mul]
  have h := det_le_relative hQ principalReference_posDef
  rw [det_principalReference, ht] at h
  convert h using 1
  ring

end D4
