import D4.PrincipalSimplexMonomial

/-! The first and second moments of the four-dimensional unit simplex. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

theorem simplex4_one : (∫ _x in standardSimplex 4 1, (1 : ℝ)) = 1 / 24 := by
  simpa using standardSimplex_monomial 4 (fun _ => 0) (r := 1) (by norm_num)

theorem simplex4_coordinate (i : Fin 4) :
    (∫ x in standardSimplex 4 1, x i) = 1 / 120 := by
  have h := standardSimplex_monomial 4 (fun j => if j = i then 1 else 0)
    (r := 1) (by norm_num)
  have hf (j : Fin 4) : ((if j = i then 1 else 0) : ℕ).factorial = 1 := by
    split_ifs <;> rfl
  simp only [pow_ite, pow_one, pow_zero, Finset.prod_ite_eq', Finset.mem_univ,
    ite_true, hf, Nat.cast_one, Finset.prod_const_one, Finset.sum_ite_eq', one_pow] at h
  norm_num at h
  exact h

theorem simplex4_coordinate_mul (i j : Fin 4) :
    (∫ x in standardSimplex 4 1, x i * x j) =
      if i = j then (1 : ℝ) / 360 else 1 / 720 := by
  have h := standardSimplex_monomial 4
    (fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0))
    (r := 1) (by norm_num)
  have hs : (∑ k : Fin 4, ((if k = i then 1 else 0) + (if k = j then 1 else 0) : ℕ)) = 2 := by
    simp [Finset.sum_add_distrib]
  have hp (x : Vec) : (∏ k : Fin 4,
      x k ^ ((if k = i then 1 else 0) + (if k = j then 1 else 0))) = x i * x j := by
    simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
      Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [hp] at h
  rw [hs] at h
  by_cases hij : i = j
  · subst j
    have hf (k : Fin 4) :
        (((if k = i then 1 else 0) + (if k = i then 1 else 0) : ℕ).factorial : ℝ) =
          if k = i then 2 else 1 := by
      split_ifs <;> norm_num
    simp_rw [hf] at h
    norm_num [Finset.prod_ite_eq'] at h
    simpa only [ite_true] using h
  · have hf (k : Fin 4) :
        (((if k = i then 1 else 0) + (if k = j then 1 else 0) : ℕ).factorial : ℝ) = 1 := by
      by_cases hki : k = i <;> by_cases hkj : k = j
      · exact (hij (hki.symm.trans hkj)).elim
      all_goals simp [hki, hkj, hij, Ne.symm hij]
    simp_rw [hf] at h
    norm_num at h
    simpa only [hij, ite_false] using h

theorem simplex4_integrable (f : Vec → ℝ) (hf : Continuous f) :
    IntegrableOn f (standardSimplex 4 1) :=
  hf.continuousOn.integrableOn_compact (standardSimplex_compact 4 1)

theorem simplex4_linear (v : Vec) :
    (∫ x in standardSimplex 4 1, dotProduct v x) = dotProduct v 1 / 120 := by
  unfold dotProduct
  rw [integral_finset_sum]
  · simp only [integral_const_mul, simplex4_coordinate, Pi.one_apply, mul_one]
    rw [← Finset.sum_mul]
    ring
  · intro i _
    exact simplex4_integrable _ (by fun_prop)

theorem simplex4_quadratic (Q : Gram) :
    (∫ x in standardSimplex 4 1, quadratic Q x) =
      (quadratic Q 1 + Q.trace) / 720 := by
  simp_rw [quadratic_eq_sum]
  rw [integral_finset_sum]
  · have hi (i : Fin 4) :
        (∫ x in standardSimplex 4 1, ∑ j, Q i j * (x i * x j)) =
          ∑ j, Q i j * ((1 : ℝ) / 720 + if i = j then 1 / 720 else 0) := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul, simplex4_coordinate_mul]
        by_cases hij : i = j <;> simp only [hij, ite_true, ite_false] <;> ring
      · intro j _
        exact simplex4_integrable _ (by fun_prop)
    simp_rw [hi]
    simp [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, Matrix.trace,
      mul_ite, mul_comm, ← add_div, div_eq_mul_inv]
  · intro i _
    exact simplex4_integrable _ (by fun_prop)

end D4.Principal
