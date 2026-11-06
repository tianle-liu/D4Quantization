import D4.Definitions
import D4.Scalar

/-!
# Conditional connection to the genuine integral

The hypotheses explicitly include the moment identity and the polynomial
bounds. This module proves the normalization step; it does not discharge
those geometric hypotheses or claim the global lattice theorem.
-/
noncomputable section
namespace D4.Analytic

theorem normalized_bound_of_numerator {Q : Gram} (hQ : Q.PosDef) (N : ℝ)
    (hmoment : 60 * Q.det * moment Q = N)
    (hbound : 13 * Real.sqrt 2 * Q.det ^ (5/4 : ℝ) ≤ N) :
    optimalConstant ≤ normalizedMoment Q := by
  have hd := hQ.det_pos
  have hr : 0 < Q.det ^ (1/4 : ℝ) := Real.rpow_pos_of_pos hd _
  have hc : 240 * optimalConstant = 13 * Real.sqrt 2 := by
    have h := D4.c1Factor_eq_target
    dsimp [D4.c1Factor, optimalConstant] at *
    linarith only [h]
  unfold normalizedMoment
  apply (le_div_iff₀ (mul_pos (by norm_num) hr)).2
  apply (mul_le_mul_left (show 0 < 60 * Q.det by positivity)).mp
  calc
    60 * Q.det * (optimalConstant * (4 * Q.det^(1/4 : ℝ))) =
        (240 * optimalConstant) * (Q.det * Q.det^(1/4 : ℝ)) := by ring
    _ = 13 * Real.sqrt 2 * Q.det^(5/4 : ℝ) := by
      rw [hc, D4.fiveFourths_eq_mul_quarter Q.det hd]
    _ ≤ N := hbound
    _ = 60 * Q.det * moment Q := hmoment.symm

theorem normalized_strict_of_principal_numerator {Q : Gram} (hQ : Q.PosDef) (S : ℝ)
    (hmoment : 12 * Q.det * moment Q = S)
    (hbound : D4.c1Factor * Q.det ^ (5/4 : ℝ) < S) :
    optimalConstant < normalizedMoment Q := by
  have hd := hQ.det_pos
  have hr : 0 < Q.det ^ (1/4 : ℝ) := Real.rpow_pos_of_pos hd _
  have hc : 48 * optimalConstant = D4.c1Factor := D4.c1Factor_eq_target.symm
  unfold normalizedMoment
  apply (lt_div_iff₀ (mul_pos (by norm_num) hr)).2
  apply (mul_lt_mul_left (show 0 < 12 * Q.det by positivity)).mp
  calc
    12 * Q.det * (optimalConstant * (4 * Q.det^(1/4 : ℝ))) =
        (48 * optimalConstant) * (Q.det * Q.det^(1/4 : ℝ)) := by ring
    _ = D4.c1Factor * Q.det^(5/4 : ℝ) := by
      rw [hc, D4.fiveFourths_eq_mul_quarter Q.det hd]
    _ < S := hbound
    _ = 12 * Q.det * moment Q := hmoment.symm

/-- The actual integral lower bound follows once these stated geometric and
polynomial obligations have been proved for a particular form. -/
theorem c23_analytic_bound_of_moment_bounds {Q : Gram} (hQ : Q.PosDef) (t N : ℝ)
    (ht : 0 < t) (hdet : Q.det ≤ 4*t^4)
    (hmoment : 60 * Q.det * moment Q = N)
    (h₁ : 20*Q.det*t ≤ N)
    (h₂ : (82/3 : ℝ)*Q.det*t-(41/4 : ℝ)*t^5 ≤ N)
    (h₃ : 31*Q.det*t-20*t^5 ≤ N) :
    optimalConstant ≤ normalizedMoment Q := by
  apply normalized_bound_of_numerator hQ N hmoment
  exact D4.c23_homogeneous_bound Q.det t N hQ.det_pos ht hdet h₁ h₂ h₃

end D4.Analytic
