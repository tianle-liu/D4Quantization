import D4.C23JointC2DiagonalTriangles
import D4.C23JointC2Corners

noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope Analytic Filter Topology
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem localWindow2_diagonalRegion_quadratic_analytic
    (p q r : P → ℝ) (η R : ℝ) (Q H : P → Gram) (u : P → Fin 3 → ℝ) (x₀ : P)
    (hp : AnalyticAt ℝ p x₀) (hq : AnalyticAt ℝ q x₀) (hr : AnalyticAt ℝ r x₀)
    (hr₀ : 0<r x₀) (hη : 0<η)
    (hQ : ∀i j,AnalyticAt ℝ (fun x => Q x i j) x₀)
    (hH : ∀i j,AnalyticAt ℝ (fun x => H x i j) x₀)
    (hu : ∀i,AnalyticAt ℝ (fun x => u x i) x₀) (i : Fin 2) :
    AnalyticAt ℝ (fun x => ∫y in localWindow2 (Q x) (affineEval (u x))
      (localRegion2 (p x) (q x) (r x) η (![3,6] i)) R,quadratic (H x) y) x₀ := by
  simp_rw [diagonalRegion2_eq _ _ _ _ hη]
  apply localWindow2_diagonal_trapezoid_quadratic_analytic R Q H u
    (fun x => diagonalOffset2 (p x) (q x) (r x) i 0)
    (fun x => diagonalOffset2 (p x) (q x) (r x) i 1)
    (fun x => diagonalTrapezoid2 (r x) η i) x₀ hQ hH hu
  · fin_cases i
    · exact analyticAt_const
    · change AnalyticAt ℝ (fun x => 2*p x) x₀; fun_prop
  · fin_cases i
    · change AnalyticAt ℝ (fun x => 2*r x) x₀; fun_prop
    · change AnalyticAt ℝ (fun x => 2*(q x+r x)) x₀; fun_prop
  · exact diagonalTrapezoid2_analytic r η x₀ hr i
  · exact diagonalTrapezoid2_valid _ _ hr₀ hη i

theorem localWindow2_cornerRegion_quadratic_analytic
    (p q r : P → ℝ) (η R : ℝ) (Q H : P → Gram) (u : P → Fin 3 → ℝ) (x₀ : P)
    (hp : AnalyticAt ℝ p x₀) (hq : AnalyticAt ℝ q x₀) (hr : AnalyticAt ℝ r x₀)
    (hη : 0<η)
    (hQ : ∀i j,AnalyticAt ℝ (fun x => Q x i j) x₀)
    (hH : ∀i j,AnalyticAt ℝ (fun x => H x i j) x₀)
    (hu : ∀i,AnalyticAt ℝ (fun x => u x i) x₀) (i : Fin 2) :
    AnalyticAt ℝ (fun x => ∫y in localWindow2 (Q x) (affineEval (u x))
      (localRegion2 (p x) (q x) (r x) η (![7,8] i)) R,quadratic (H x) y) x₀ := by
  simp_rw [cornerRegion2_eq _ _ _ _ hη]
  apply localWindow2_affine_quadratic_analytic
    (Principal.standardSimplex 2 1) (Principal.standardSimplex_compact 2 1) R Q H
    (fun _ => cornerMatrix2 η i) (fun x => cornerOrigin2 (p x) (q x) (r x) i) u x₀ hQ hH
  · intro j k; exact analyticAt_const
  · intro j
    fin_cases i <;> fin_cases j
    · exact analyticAt_const
    · change AnalyticAt ℝ (fun x => 2*(q x+r x)) x₀; fun_prop
    · change AnalyticAt ℝ (fun x => 2*(p x+r x)) x₀; fun_prop
    · exact analyticAt_const
  · exact hu
  · rw [cornerMatrix2_det]
    exact neg_ne_zero.mpr (pow_ne_zero 2 hη.ne')

end D4.C23Local
