import D4.FixedQuadraticIntegralAnalytic

/-! Joint analyticity of finite polynomial integrals on a fixed reference
window and of nonsingular linear systems. The parameter space is arbitrary. -/
noncomputable section
namespace D4.ParameterAnalytic
open Matrix MeasureTheory Set C23Local

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Spatial factors need only be continuous. All dependence on the parameters
is in finitely many analytic coefficients, so integration is a finite sum. -/
theorem integral_prod_sum (S : Set WindowCoordinates) (hS : IsCompact S)
    (m k : ℕ) (a : P → Fin m → Fin k → ℝ)
    (b : Fin m → Fin k → WindowCoordinates → ℝ) (p₀ : P)
    (ha : ∀ j i, AnalyticAt ℝ (fun p => a p j i) p₀)
    (hb : ∀ j i, Continuous (b j i)) :
    AnalyticAt ℝ (fun p => ∫ x in S,
      ∏ j : Fin m, ∑ i : Fin k, a p j i * b j i x) p₀ := by
  have he (p : P) (x : WindowCoordinates) :
      (∏ j : Fin m, ∑ i : Fin k, a p j i * b j i x) =
        ∑ f : Fin m → Fin k, (∏ j : Fin m, a p j (f j)) *
          (∏ j : Fin m, b j (f j) x) := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f _
    exact Finset.prod_mul_distrib
  have hb' (f : Fin m → Fin k) : Continuous (fun x => ∏ j : Fin m, b j (f j) x) :=
    continuous_finset_prod _ (fun j _ => hb j (f j))
  have heq (p : P) : (∫ x in S, ∏ j : Fin m, ∑ i : Fin k, a p j i*b j i x) =
      ∑ f : Fin m → Fin k, (∏ j : Fin m, a p j (f j)) *
        (∫ x in S, ∏ j : Fin m, b j (f j) x) := by
    simp_rw [he]
    rw [integral_finset_sum _ (fun f _ =>
      ((hb' f).continuousOn.integrableOn_compact hS).const_mul _)]
    simp only [integral_const_mul]
  simp_rw [heq]
  apply Finset.analyticAt_sum
  intro f _
  exact (Finset.analyticAt_prod _ (fun j _ => ha j (f j))).mul analyticAt_const

theorem matrix_det {n : Type*} [Fintype n] [DecidableEq n]
    (B : P → Matrix n n ℝ) (p₀ : P)
    (hB : ∀ i j, AnalyticAt ℝ (fun p => B p i j) p₀) :
    AnalyticAt ℝ (fun p => (B p).det) p₀ := by
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  exact Finset.analyticAt_prod _ (fun i _ => hB (σ i) i)

theorem matrix_adjugate {n : Type*} [Fintype n] [DecidableEq n]
    (B : P → Matrix n n ℝ) (p₀ : P)
    (hB : ∀ i j, AnalyticAt ℝ (fun p => B p i j) p₀) (i j : n) :
    AnalyticAt ℝ (fun p => (B p).adjugate i j) p₀ := by
  simp only [Matrix.adjugate_apply]
  apply matrix_det
  intro u v
  by_cases hu : u=j
  · subst u
    simp only [Matrix.updateRow_self]
    exact analyticAt_const
  · simp only [Matrix.updateRow_ne hu]
    exact hB u v

theorem matrix_inv {n : Type*} [Fintype n] [DecidableEq n]
    (B : P → Matrix n n ℝ) (p₀ : P)
    (hB : ∀ i j, AnalyticAt ℝ (fun p => B p i j) p₀)
    (hdet : (B p₀).det ≠ 0) (i j : n) :
    AnalyticAt ℝ (fun p => (B p)⁻¹ i j) p₀ := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact ((matrix_det B p₀ hB).inv hdet).mul (matrix_adjugate B p₀ hB i j)

theorem linear_system_solution {n : Type*} [Fintype n] [DecidableEq n]
    (B : P → Matrix n n ℝ) (b : P → n → ℝ) (p₀ : P)
    (hB : ∀ i j, AnalyticAt ℝ (fun p => B p i j) p₀)
    (hb : ∀ i, AnalyticAt ℝ (fun p => b p i) p₀)
    (hdet : (B p₀).det ≠ 0) (i : n) :
    AnalyticAt ℝ (fun p => ((B p)⁻¹ *ᵥ b p) i) p₀ := by
  unfold Matrix.mulVec dotProduct
  exact Finset.analyticAt_sum _ (fun j _ =>
    (matrix_inv B p₀ hB hdet i j).mul (hb j))

end D4.ParameterAnalytic
