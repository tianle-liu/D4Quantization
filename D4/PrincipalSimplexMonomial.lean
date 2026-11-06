import D4.PrincipalSimplex
import D4.PrincipalBeta

/-! Exact monomial integration on a simplex, by dimension induction. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

theorem standardSimplex_monomial (n : ℕ) (k : Fin n → ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in standardSimplex n r, ∏ i, x i ^ k i) =
      (∏ i, (k i).factorial : ℝ) / (n + ∑ i, k i).factorial * r ^ (n + ∑ i, k i) := by
  induction n generalizing r with
  | zero =>
    have hs : standardSimplex 0 r = Set.univ := by ext x; simp [standardSimplex, hr]
    simp [hs, volume_pi, measureReal_def]
  | succ n ih =>
    rw [standardSimplex_integral_succ n r _ (by fun_prop)]
    let N := n + ∑ i : Fin n, k i.succ
    let C : ℝ := (∏ i : Fin n, (k i.succ).factorial : ℝ) / N.factorial
    have inner (t : ℝ) (ht : t ∈ Icc 0 r) :
        (∫ y in standardSimplex n (r - t), ∏ i, (Fin.cons t y) i ^ k i) =
          C * (t ^ k 0 * (r - t) ^ N) := by
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [integral_const_mul, ih _ (sub_nonneg.mpr ht.2)]
      dsimp [C, N]
      ring
    calc
      _ = ∫ t in Icc 0 r, C * (t ^ k 0 * (r - t) ^ N) :=
        setIntegral_congr_fun measurableSet_Icc inner
      _ = C * ((k 0).factorial * N.factorial / (k 0 + N + 1).factorial *
          r ^ (k 0 + N + 1)) := by
        rw [integral_const_mul, integral_pow_mul_sub_pow _ _ hr]
      _ = _ := by
        have hdegree : n + 1 + ∑ i : Fin (n + 1), k i = k 0 + N + 1 := by
          rw [Fin.sum_univ_succ]
          dsimp [N]
          omega
        rw [hdegree, Fin.prod_univ_succ]
        dsimp [C]
        have hn : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
        field_simp
        ring

end D4.Principal
