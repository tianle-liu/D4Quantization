import D4.PolynomialDeterminants
import D4.CertificateTargets
import D4.Determinant
import D4.Reduction

/-!
# The certified polynomial bounds on the actual secondary cones

The determinant inputs are identified with actual matrix determinants.
All nine polynomial inequalities, determinant estimates, and scalar steps
are discharged. The analytic corollaries use explicit moment-integral
interfaces, discharged by the geometric formulas in `D4.CompleteTheoremA`.
-/
noncomputable section
namespace D4.CertifiedPolynomials
open Matrix Certificate CertificateMoments

/-- The principal-cone scale is the sum of its ten actual weights. -/
theorem L_eq_sum (x : Nat → ℝ) : L x = ∑ i : Fin 10, x i := by
  norm_num [L, parameterC1, eval, monomial, Fin.sum_univ_succ]

/-- The second-cone scale equals its proven matrix-trace parameter. -/
theorem t2_eq_parameter (x : Nat → ℝ) :
    t2 x = secondaryTraceParameter (x 0) (fun i => x (i+1)) := by
  norm_num [t2, parameterC2, eval, monomial, secondaryTraceParameter, Fin.sum_univ_succ]
  ring

/-- The third-cone scale uses the same parameter ordering. -/
theorem t3_eq_parameter (x : Nat → ℝ) :
    t3 x = secondaryTraceParameter (x 0) (fun i => x (i+1)) := by
  norm_num [t3, parameterC3, eval, monomial, secondaryTraceParameter, Fin.sum_univ_succ]
  ring

theorem D1_eq_det (x : Nat → ℝ) : D1 x = (principalForm (fun i => x i)).det :=
  determinantC1_eval x

theorem D2_eq_det (x : Nat → ℝ) :
    D2 x = (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).det :=
  determinantC2_eval x

theorem D3_eq_det (x : Nat → ℝ) :
    D3 x = (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).det :=
  determinantC3_eval x

/-- Positivity of the actual principal form forces a positive scale. -/
theorem L_pos (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (principalForm (fun i => x i)).PosDef) : 0 < L x := by
  have hn : 0 ≤ L x := by rw [L_eq_sum]; exact Finset.sum_nonneg (fun i _ => hx i)
  by_contra h
  have hz : L x = 0 := le_antisymm (le_of_not_gt h) hn
  have hd := det_principal_le (fun i => x i) hQ
  rw [← L_eq_sum, hz] at hd
  norm_num at hd
  exact (not_le_of_gt hQ.det_pos) hd

theorem t2_pos (x : Nat → ℝ)
    (hQ : (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).PosDef) : 0 < t2 x := by
  rw [t2_eq_parameter]
  exact secondaryTraceParameter_pos cone2_trace_normalization _ _ hQ

theorem t3_pos (x : Nat → ℝ)
    (hQ : (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).PosDef) : 0 < t3 x := by
  rw [t3_eq_parameter]
  exact secondaryTraceParameter_pos cone3_trace_normalization _ _ hQ

/-- The first-cone polynomial comparison, with all algebraic premises proved. -/
theorem principal_polynomial_strict (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (principalForm (fun i => x i)).PosDef) :
    c1Factor * (principalForm (fun i => x i)).det ^ (5/4 : ℝ) < S x := by
  apply c1_homogeneous_strict _ (L x) (S x) hQ.det_pos (L_pos x hx hQ)
  · rw [L_eq_sum]
    exact det_principal_le _ hQ
  · simpa only [D1_eq_det] using c1_base x hx
  · simpa only [D1_eq_det] using c1_middle x hx
  · simpa only [D1_eq_det] using c1_high x hx

/-- The second-cone polynomial comparison, with all algebraic premises proved. -/
theorem secondary2_polynomial_bound (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).PosDef) :
    13 * Real.sqrt 2 * (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).det ^
      (5/4 : ℝ) ≤ N2 x := by
  apply c23_homogeneous_bound _ (t2 x) (N2 x) hQ.det_pos (t2_pos x hQ)
  · rw [t2_eq_parameter]
    exact det_secondary2_le _ _ hQ
  · simpa only [D2_eq_det] using c2_base x hx
  · simpa only [D2_eq_det] using c2_middle x hx
  · simpa only [D2_eq_det] using c2_high x hx

/-- The third-cone polynomial comparison, with all algebraic premises proved. -/
theorem secondary3_polynomial_bound (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).PosDef) :
    13 * Real.sqrt 2 * (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).det ^
      (5/4 : ℝ) ≤ N3 x := by
  apply c23_homogeneous_bound _ (t3 x) (N3 x) hQ.det_pos (t3_pos x hQ)
  · rw [t3_eq_parameter]
    exact det_secondary3_le _ _ hQ
  · simpa only [D3_eq_det] using c3_base x hx
  · simpa only [D3_eq_det] using c3_middle x hx
  · simpa only [D3_eq_det] using c3_high x hx

/-- Equality for the second-cone polynomial forces the actual D₄ Gram ray. -/
theorem secondary2_polynomial_equality (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).PosDef)
    (heq : N2 x = 13 * Real.sqrt 2 *
      (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).det ^ (5/4 : ℝ)) :
    secondaryForm cone2Vectors (x 0) (fun i => x (i+1)) = t2 x • gramMatrix ℝ := by
  have hd : (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).det = 4*(t2 x)^4 := by
    apply c23_homogeneous_equality_forces_det _ (t2 x) (N2 x)
      hQ.det_pos (t2_pos x hQ) _ _ _ _ heq
    · rw [t2_eq_parameter]
      exact det_secondary2_le _ _ hQ
    · simpa only [D2_eq_det] using c2_base x hx
    · simpa only [D2_eq_det] using c2_middle x hx
    · simpa only [D2_eq_det] using c2_high x hx
  rw [t2_eq_parameter] at hd ⊢
  exact (det_secondary2_eq_iff _ _ hQ).mp hd

/-- Equality for the third-cone polynomial forces the actual D₄ Gram ray. -/
theorem secondary3_polynomial_equality (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).PosDef)
    (heq : N3 x = 13 * Real.sqrt 2 *
      (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).det ^ (5/4 : ℝ)) :
    secondaryForm cone3Vectors (x 0) (fun i => x (i+1)) = t3 x • gramMatrix ℝ := by
  have hd : (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).det = 4*(t3 x)^4 := by
    apply c23_homogeneous_equality_forces_det _ (t3 x) (N3 x)
      hQ.det_pos (t3_pos x hQ) _ _ _ _ heq
    · rw [t3_eq_parameter]
      exact det_secondary3_le _ _ hQ
    · simpa only [D3_eq_det] using c3_base x hx
    · simpa only [D3_eq_det] using c3_middle x hx
    · simpa only [D3_eq_det] using c3_high x hx
  rw [t3_eq_parameter] at hd ⊢
  exact (det_secondary3_eq_iff _ _ hQ).mp hd

/-- Equality of the genuine normalized moment determines its exact numerator. -/
theorem numerator_eq_of_normalized_eq {Q : Analytic.Gram} (hQ : Q.PosDef) (N : ℝ)
    (hmoment : 60 * Q.det * Analytic.moment Q = N)
    (heq : Analytic.normalizedMoment Q = Analytic.optimalConstant) :
    N = 13 * Real.sqrt 2 * Q.det ^ (5/4 : ℝ) := by
  have hr : 0 < 4 * Q.det ^ (1/4 : ℝ) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hQ.det_pos _)
  have hM : Analytic.moment Q = Analytic.optimalConstant * (4 * Q.det ^ (1/4 : ℝ)) :=
    (div_eq_iff hr.ne').mp heq
  have hc : 240 * Analytic.optimalConstant = 13 * Real.sqrt 2 := by
    have h := c1Factor_eq_target
    dsimp [c1Factor, Analytic.optimalConstant] at *
    linarith only [h]
  calc
    N = 60 * Q.det * Analytic.moment Q := hmoment.symm
    _ = (240 * Analytic.optimalConstant) * (Q.det * Q.det ^ (1/4 : ℝ)) := by rw [hM]; ring
    _ = 13 * Real.sqrt 2 * Q.det ^ (5/4 : ℝ) := by
      rw [hc, fiveFourths_eq_mul_quarter Q.det hQ.det_pos]

/-- The principal-cone analytic conclusion now requires only its actual moment identity. -/
theorem principal_analytic_of_moment_identity (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (principalForm (fun i => x i)).PosDef)
    (hmoment : 12 * (principalForm (fun i => x i)).det *
      Analytic.moment (principalForm (fun i => x i)) = S x) :
    Analytic.optimalConstant < Analytic.normalizedMoment (principalForm (fun i => x i)) :=
  Analytic.normalized_strict_of_principal_numerator hQ (S x) hmoment
    (principal_polynomial_strict x hx hQ)

/-- The second-cone analytic conclusion requires only its actual moment identity. -/
theorem secondary2_analytic_of_moment_identity (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).PosDef)
    (hmoment : 60 * (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).det *
      Analytic.moment (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))) = N2 x) :
    Analytic.optimalConstant ≤
      Analytic.normalizedMoment (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))) :=
  Analytic.normalized_bound_of_numerator hQ (N2 x) hmoment
    (secondary2_polynomial_bound x hx hQ)

/-- The third-cone analytic conclusion requires only its actual moment identity. -/
theorem secondary3_analytic_of_moment_identity (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).PosDef)
    (hmoment : 60 * (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).det *
      Analytic.moment (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))) = N3 x) :
    Analytic.optimalConstant ≤
      Analytic.normalizedMoment (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))) :=
  Analytic.normalized_bound_of_numerator hQ (N3 x) hmoment
    (secondary3_polynomial_bound x hx hQ)

/-- Analytic equality on the second cone forces the actual D₄ Gram ray,
conditional only on the moment-integral identity. -/
theorem secondary2_analytic_equality (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).PosDef)
    (hmoment : 60 * (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).det *
      Analytic.moment (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))) = N2 x)
    (heq : Analytic.normalizedMoment (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))) =
      Analytic.optimalConstant) :
    secondaryForm cone2Vectors (x 0) (fun i => x (i+1)) = t2 x • gramMatrix ℝ :=
  secondary2_polynomial_equality x hx hQ
    (numerator_eq_of_normalized_eq hQ (N2 x) hmoment heq)

/-- Analytic equality on the third cone forces the actual D₄ Gram ray,
conditional only on the moment-integral identity. -/
theorem secondary3_analytic_equality (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).PosDef)
    (hmoment : 60 * (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).det *
      Analytic.moment (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))) = N3 x)
    (heq : Analytic.normalizedMoment (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))) =
      Analytic.optimalConstant) :
    secondaryForm cone3Vectors (x 0) (fun i => x (i+1)) = t3 x • gramMatrix ℝ :=
  secondary3_polynomial_equality x hx hQ
    (numerator_eq_of_normalized_eq hQ (N3 x) hmoment heq)

end D4.CertifiedPolynomials
