import D4.CompactParameters
import D4.PolynomialDeterminants

set_option maxHeartbeats 0
noncomputable section
namespace D4.CompactMoments
open Matrix Certificate CertificateMoments

theorem z2_coordinates (x : Nat → ℝ) :
    (fun i : Fin 10 => z2 x i) =
      ![x 1+x 0, x 2+x 0, x 3, x 4, -x 0, x 5+x 0,
        x 6+x 0, x 7+x 0, x 8+x 0, x 9] := by
  ext i
  fin_cases i <;> simp [z2, z2Substitution, eval, monomial, add_comm]

theorem theta_coordinates (x : Nat → ℝ) :
    (fun i : Fin 10 => theta x i) =
      ![x 0+x 9, x 1-x 9, x 2-x 9, x 3, x 4,
        x 5, x 6, x 7, x 8, -x 9] := by
  ext i
  fin_cases i <;> simp [theta, thetaSubstitution, eval, monomial, sub_eq_add_neg]

theorem secondary2_eq_principal (x : Nat → ℝ) :
    secondaryForm cone2Vectors (x 0) (fun i => x (i+1)) =
      principalForm (fun i => z2 x i) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondaryForm, principalForm, rankOne, cone2Vectors,
      cone1Vectors, gramMatrix, z2, z2Substitution, eval, monomial,
      Fin.sum_univ_succ] <;> ring

theorem secondary3_eq_secondary2 (x : Nat → ℝ) :
    secondaryForm cone3Vectors (x 0) (fun i => x (i+1)) =
      secondaryForm cone2Vectors (theta x 0) (fun i => theta x (i+1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondaryForm, rankOne, cone2Vectors, cone3Vectors,
      gramMatrix, theta, thetaSubstitution, eval, monomial,
      Fin.sum_univ_succ] <;> ring

theorem determinantC2_compact (x : Nat → ℝ) :
    eval x determinantC2 = eval (z2 x) determinantC1 := by
  rw [determinantC2_eval, secondary2_eq_principal, determinantC1_eval]

theorem determinantC3_compact (x : Nat → ℝ) :
    eval x determinantC3 = eval (theta x) determinantC2 := by
  rw [determinantC3_eval, secondary3_eq_secondary2, determinantC2_eval]

end D4.CompactMoments
