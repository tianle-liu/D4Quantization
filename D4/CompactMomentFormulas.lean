import D4.CompactMomentC2Checks
import D4.CompactMomentC3Checks
import D4.CompactMomentMatrices

noncomputable section
namespace D4.CompactMoments
open Certificate CertificateMoments

theorem correction2_eval (x : Nat → ℝ) :
    eval x correction2 = 2*(x 0)^3 *
      (2*(x 0)^2 + 5*x 0*(x 3+x 4+x 9) +
        10*(x 3*x 4+x 3*x 9+x 4*x 9)) := by
  simp only [correction2, eval_cons, eval_nil, monomial, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil]
  norm_num
  ring

theorem correction3_eval (x : Nat → ℝ) :
    eval x correction3 = 2*(x 9)^3 *
      (3*(x 9)^2 - 5*x 9*(x 1+x 2) + 10*x 1*x 2) := by
  simp only [correction3, eval_cons, eval_nil, monomial, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil]
  norm_num
  ring

/-- The first compact polynomial identity, with no positivity restriction. -/
theorem momentC2_compact (x : Nat → ℝ) :
    eval x momentC2 = 5*eval (z2 x) momentC1 +
      2*(x 0)^3 * (2*(x 0)^2 + 5*x 0*(x 3+x 4+x 9) +
        10*(x 3*x 4+x 3*x 9+x 4*x 9)) := by
  have h := congrArg (eval x) compact2_check
  rw [eval_sumFast] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, eval_scale, Int.cast_ofNat,
    substituted2_eval, correction2_eval] at h
  exact h.symm

/-- The second compact polynomial identity, with no positivity restriction. -/
theorem momentC3_compact (x : Nat → ℝ) :
    eval x momentC3 = eval (theta x) momentC2 +
      2*(x 9)^3 * (3*(x 9)^2 - 5*x 9*(x 1+x 2) + 10*x 1*x 2) := by
  have h := congrArg (eval x) compact3_check
  rw [eval_sumFast] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, substituted3_eval, correction3_eval] at h
  exact h.symm

end D4.CompactMoments
