import D4.PrincipalSimplexVertices
import D4.AreaTriangles

/-! Analyticity of genuine quadratic integrals on moving nondegenerate
four-dimensional simplices. -/
noncomputable section
namespace D4.Analytic
open Matrix MeasureTheory Set Principal

theorem analyticAt_matrix_det {n : Type*} [Fintype n] [DecidableEq n]
    (B : ℝ → Matrix n n ℝ) (t₀ : ℝ)
    (hB : ∀ i j, AnalyticAt ℝ (fun t => B t i j) t₀) :
    AnalyticAt ℝ (fun t => (B t).det) t₀ := by
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  exact Finset.analyticAt_prod _ (fun i _ => hB (σ i) i)

theorem analyticAt_quadratic (Q : ℝ → Gram) (v : ℝ → Vec) (t₀ : ℝ)
    (hQ : ∀ i j, AnalyticAt ℝ (fun t => Q t i j) t₀)
    (hv : ∀ i, AnalyticAt ℝ (fun t => v t i) t₀) :
    AnalyticAt ℝ (fun t => quadratic (Q t) (v t)) t₀ := by
  unfold quadratic dotProduct Matrix.mulVec
  apply Finset.analyticAt_sum
  intro i _
  apply (hv i).mul
  exact Finset.analyticAt_sum _ (fun j _ => (hQ i j).mul (hv j))

theorem simplexMatrix_sub (v : Fin 5 → Vec) (a : Vec) :
    simplexMatrix (fun i => v i-a) = simplexMatrix v := by
  ext i j
  simp only [simplexMatrix, Pi.sub_apply]
  ring

theorem vertexSimplex_quadratic_shift {Q : Gram} (hQ : Q.IsHermitian)
    (v : Fin 5 → Vec) (hv : (simplexMatrix v).det ≠ 0) (a : Vec) :
    (∫ x in vertexSimplex v, quadratic Q (x-a)) =
      |(simplexMatrix v).det| / 720 *
        (quadratic Q (∑ i, (v i-a)) + ∑ i, quadratic Q (v i-a)) := by
  have hh := vertexSimplex_quadratic hQ (fun i => v i-a) (by rwa [simplexMatrix_sub])
  rw [simplexMatrix_sub] at hh
  rw [← hh]
  unfold vertexSimplex
  rw [simplexMatrix_sub, affineSimplex_integral _ hv,
    affineSimplex_integral _ hv]
  congr 1
  apply setIntegral_congr_fun (standardSimplex_closed 4 1).measurableSet
  intro x _
  apply congrArg (quadratic Q)
  dsimp
  abel

theorem analyticAt_vertexSimplex_quadratic_shift (Q : ℝ → Gram)
    (v : ℝ → Fin 5 → Vec) (a : ℝ → Vec) (t₀ : ℝ)
    (hQ : ∀ i j, AnalyticAt ℝ (fun t => Q t i j) t₀)
    (hv : ∀ i j, AnalyticAt ℝ (fun t => v t i j) t₀)
    (ha : ∀ j, AnalyticAt ℝ (fun t => a t j) t₀)
    (hdet : (simplexMatrix (v t₀)).det ≠ 0)
    (hherm : ∀ᶠ t in nhds t₀, (Q t).IsHermitian) :
    AnalyticAt ℝ (fun t => ∫ x in vertexSimplex (v t),
      quadratic (Q t) (x-a t)) t₀ := by
  have hmatrix (i j : Fin 4) : AnalyticAt ℝ (fun t => simplexMatrix (v t) i j) t₀ :=
    (hv j.succ i).sub (hv 0 i)
  have hd := analyticAt_matrix_det (fun t => simplexMatrix (v t)) t₀ hmatrix
  have habs := AreaEnvelope.analyticAt_abs_of_ne_zero _ t₀ hd hdet
  have hshift (i : Fin 5) (j : Fin 4) :
      AnalyticAt ℝ (fun t => (v t i-a t) j) t₀ := (hv i j).sub (ha j)
  have hsum (j : Fin 4) :
      AnalyticAt ℝ (fun t => (∑ i : Fin 5, (v t i-a t)) j) t₀ := by
    simp only [Finset.sum_apply]
    exact Finset.analyticAt_sum _ (fun i _ => hshift i j)
  have hqsum := analyticAt_quadratic Q (fun t => ∑ i : Fin 5, (v t i-a t)) t₀ hQ hsum
  have hsumq := Finset.analyticAt_sum Finset.univ (fun i _ =>
    analyticAt_quadratic Q (fun t => v t i-a t) t₀ hQ (hshift i))
  apply ((habs.div analyticAt_const (by norm_num : (720:ℝ) ≠ 0)).mul
    (hqsum.add hsumq)).congr
  filter_upwards [hd.continuousAt.eventually_ne hdet,hherm] with t ht hQt
  exact (vertexSimplex_quadratic_shift hQt (v t) ht (a t)).symm

end D4.Analytic
