import D4.MovingSimplexAnalytic

/-! Nonsingular systems with analytic entries have analytic solutions. -/
noncomputable section
namespace D4.Analytic
open Matrix

theorem analyticAt_matrix_adjugate {n : Type*} [Fintype n] [DecidableEq n]
    (B : ℝ → Matrix n n ℝ) (t₀ : ℝ)
    (hB : ∀ i j, AnalyticAt ℝ (fun t => B t i j) t₀) (i j : n) :
    AnalyticAt ℝ (fun t => (B t).adjugate i j) t₀ := by
  simp only [Matrix.adjugate_apply]
  apply analyticAt_matrix_det
  intro k l
  by_cases hk : k=j
  · subst k
    simp only [Matrix.updateRow_self]
    exact analyticAt_const
  · simp only [Matrix.updateRow_ne hk]
    exact hB k l

theorem analyticAt_matrix_inv {n : Type*} [Fintype n] [DecidableEq n]
    (B : ℝ → Matrix n n ℝ) (t₀ : ℝ)
    (hB : ∀ i j, AnalyticAt ℝ (fun t => B t i j) t₀)
    (hdet : (B t₀).det ≠ 0) (i j : n) :
    AnalyticAt ℝ (fun t => (B t)⁻¹ i j) t₀ := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact ((analyticAt_matrix_det B t₀ hB).inv hdet).mul
    (analyticAt_matrix_adjugate B t₀ hB i j)

theorem analyticAt_linear_system_solution {n : Type*} [Fintype n] [DecidableEq n]
    (B : ℝ → Matrix n n ℝ) (b : ℝ → n → ℝ) (t₀ : ℝ)
    (hB : ∀ i j, AnalyticAt ℝ (fun t => B t i j) t₀)
    (hb : ∀ i, AnalyticAt ℝ (fun t => b t i) t₀)
    (hdet : (B t₀).det ≠ 0) (i : n) :
    AnalyticAt ℝ (fun t => ((B t)⁻¹ *ᵥ b t) i) t₀ := by
  unfold Matrix.mulVec dotProduct
  exact Finset.analyticAt_sum _ (fun j _ =>
    (analyticAt_matrix_inv B t₀ hB hdet i j).mul (hb j))

theorem linear_system_solution_unique {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℝ) (b : n → ℝ) (hdet : B.det ≠ 0) (x : n → ℝ) :
    B *ᵥ x=b ↔ x=B⁻¹ *ᵥ b := by
  constructor
  · intro h
    have hh := congrArg (fun y => B⁻¹ *ᵥ y) h
    simpa only [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec] using hh
  · rintro rfl
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]

end D4.Analytic
