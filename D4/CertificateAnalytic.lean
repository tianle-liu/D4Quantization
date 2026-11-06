import D4.Certificate
import Mathlib.Analysis.Analytic.Constructions

/-! Polynomial certificate evaluation preserves analytic dependence. -/
noncomputable section
namespace D4.Certificate

theorem monomial_analyticAt (x : ℝ → Nat → ℝ) (t₀ : ℝ)
    (hx : ∀ i, AnalyticAt ℝ (fun t => x t i) t₀) (m : Monomial) :
    AnalyticAt ℝ (fun t => monomial (x t) m) t₀ := by
  induction m with
  | nil => exact analyticAt_const
  | cons i m ih =>
    simpa only [monomial,List.map_cons,List.prod_cons] using (hx i).mul ih

theorem eval_analyticAt (x : ℝ → Nat → ℝ) (t₀ : ℝ)
    (hx : ∀ i, AnalyticAt ℝ (fun t => x t i) t₀) (p : Poly) :
    AnalyticAt ℝ (fun t => eval (x t) p) t₀ := by
  induction p with
  | nil => exact analyticAt_const
  | cons s p ih =>
    simpa only [eval_cons] using
      (analyticAt_const.mul (monomial_analyticAt x t₀ hx s.1)).add ih

end D4.Certificate
