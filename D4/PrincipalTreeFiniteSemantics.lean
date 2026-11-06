import D4.PrincipalTreeTensorSemantics
import D4.PrincipalMoment

noncomputable section
namespace D4.Principal
open Matrix Analytic Certificate

def upperContraction (A T : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 0 0*T 0 0 + 2*(A 0 1*T 0 1) + 2*(A 0 2*T 0 2) + 2*(A 0 3*T 0 3) +
  A 1 1*T 1 1 + 2*(A 1 2*T 1 2) + 2*(A 1 3*T 1 3) +
  A 2 2*T 2 2 + 2*(A 2 3*T 2 3) + A 3 3*T 3 3

theorem symmetric_contraction_eq_upper (A T : Matrix (Fin 4) (Fin 4) ℝ)
    (ha : ∀ i j, A i j = A j i) (ht : ∀ i j, T i j = T j i) :
    (∑ i, ∑ j, A i j*T i j) = upperContraction A T := by
  simp [Fin.sum_univ_succ, upperContraction]
  norm_num only
  rw [ha 1 0, ha 2 0, ha 3 0, ha 2 1, ha 3 1, ha 3 2,
    ht 1 0, ht 2 0, ht 3 0, ht 2 1, ht 3 1, ht 3 2]
  ring

theorem treeMomentNumerator_eq_upper (w : Fin 10 → ℝ) :
    treeMomentNumerator w = upperContraction (principalForm w).adjugate (treeTensor w) := by
  have hsum : treeMomentNumerator w =
      ∑ i, ∑ j, (principalForm w).adjugate i j * treeTensor w i j := by
    rw [treeTensor_contraction]
    rfl
  rw [hsum]
  apply symmetric_contraction_eq_upper
  · intro i j
    simpa using (principal_isHermitian w).adjugate.apply j i
  · exact treeTensor_symmetric w

end D4.Principal
