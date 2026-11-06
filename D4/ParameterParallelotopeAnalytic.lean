import D4.ParameterQuadraticIntegralAnalytic
import D4.PrincipalIntegral

/-! Joint analyticity of actual quadratic integrals over nondegenerate moving parallelotopes. -/
noncomputable section
namespace D4.ParameterAnalytic
open Analytic Principal Matrix MeasureTheory Set
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem abs_of_ne (f : P → ℝ) (p₀ : P) (hf : AnalyticAt ℝ f p₀)
    (hne : f p₀ ≠ 0) : AnalyticAt ℝ (fun p => |f p|) p₀ := by
  rcases lt_or_gt_of_ne hne with hn | hp
  · apply hf.neg.congr
    filter_upwards [hf.continuousAt.eventually_lt_const hn] with p h
    exact (abs_of_neg h).symm
  · apply hf.congr
    filter_upwards [hf.continuousAt.eventually_const_lt hp] with p h
    exact (abs_of_pos h).symm

theorem quadratic (Q : P → Gram) (c : P → Vec) (p₀ : P)
    (hQ : ∀ i j, AnalyticAt ℝ (fun p => Q p i j) p₀)
    (hc : ∀ i, AnalyticAt ℝ (fun p => c p i) p₀) :
    AnalyticAt ℝ (fun p => Analytic.quadratic (Q p) (c p)) p₀ := by
  simp only [Analytic.quadratic, dotProduct, Matrix.mulVec]
  apply Finset.analyticAt_sum
  intro i _
  exact (hc i).mul (Finset.analyticAt_sum _ fun j _ => (hQ i j).mul (hc j))

theorem matrix_mul (A B : P → Gram) (p₀ : P)
    (hA : ∀ i j, AnalyticAt ℝ (fun p => A p i j) p₀)
    (hB : ∀ i j, AnalyticAt ℝ (fun p => B p i j) p₀) (i j : Fin 4) :
    AnalyticAt ℝ (fun p => (A p * B p) i j) p₀ := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_sum _ fun k _ => (hA i k).mul (hB k j)

theorem integral_parallelotope_quadratic (Q B : P → Gram) (c : P → Vec) (p₀ : P)
    (hQ : ∀ i j, AnalyticAt ℝ (fun p => Q p i j) p₀)
    (hB : ∀ i j, AnalyticAt ℝ (fun p => B p i j) p₀)
    (hc : ∀ i, AnalyticAt ℝ (fun p => c p i) p₀)
    (hHerm : ∀ p, (Q p).IsHermitian) (hdet : (B p₀).det ≠ 0) :
    AnalyticAt ℝ (fun p => ∫ x in parallelotope (B p) (c p),
      Analytic.quadratic (Q p) x) p₀ := by
  have hd := matrix_det B p₀ hB
  have ha := abs_of_ne (fun p => (B p).det) p₀ hd hdet
  have hm := matrix_mul (fun p => (B p)ᵀ * Q p) B p₀
    (matrix_mul (fun p => (B p)ᵀ) Q p₀ (fun i j => hB j i) hQ) hB
  have ht : AnalyticAt ℝ (fun p => ((B p)ᵀ * Q p * B p).trace) p₀ := by
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.analyticAt_sum _ fun i _ => hm i i
  have hh : AnalyticAt ℝ (fun p => (16:ℝ)*|(B p).det| *
      (Analytic.quadratic (Q p) (c p)+((B p)ᵀ*Q p*B p).trace/3)) p₀ :=
    (analyticAt_const.mul ha).mul
      ((quadratic Q c p₀ hQ hc).add (ht.div analyticAt_const (by norm_num : (3:ℝ) ≠ 0)))
  apply hh.congr
  filter_upwards [hd.continuousAt.eventually_ne hdet] with p hp
  exact (parallelotope_quadratic (hHerm p) (B p) hp (c p)).symm

end D4.ParameterAnalytic
