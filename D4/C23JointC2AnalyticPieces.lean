import D4.C23JointC2Corners
import D4.C23JointC2Measure

noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope Filter Topology
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem localLower2_analytic (r : P → ℝ) (x₀ : P) (hr : AnalyticAt ℝ r x₀)
    (i : Fin 9) (j : Fin 3) : AnalyticAt ℝ (fun x => localLower2 (r x) i j) x₀ := by
  fin_cases i <;> fin_cases j
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (1 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (1 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-2*r x : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (1 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (1 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (1 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (1 : ℝ)) x₀
    fun_prop


theorem localDistance2_analytic (p q r : P → ℝ) (x₀ : P)
    (hp : AnalyticAt ℝ p x₀) (hq : AnalyticAt ℝ q x₀) (hr : AnalyticAt ℝ r x₀)
    (i : Fin 9) (j : Fin 3) : AnalyticAt ℝ (fun x => localDistance2 (p x) (q x) (r x) i j) x₀ := by
  fin_cases i <;> fin_cases j
  · change AnalyticAt ℝ (fun x : P => (-(0)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(1)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(1)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(-2*r x)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(1)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(1)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(2*(p x+r x)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(-1) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(2*(q x+r x)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(-1) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(2*(p x+q x+r x)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(-1) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(-1) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(2*(q x+r x)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(1)-(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(-1) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(2*(p x+r x)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(0)-(-1) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (-(1)-(0) : ℝ)) x₀
    fun_prop


theorem rectangularTrapezoid2_analytic (p q r : P → ℝ) (η : ℝ) (x₀ : P)
    (hp : AnalyticAt ℝ p x₀) (hq : AnalyticAt ℝ q x₀) (hr : AnalyticAt ℝ r x₀)
    (i : Fin 4) (j : Fin 6) :
    AnalyticAt ℝ (fun x => (rectangularTrapezoid2 (p x) (q x) (r x) η i).coordinate j) x₀ := by
  fin_cases i <;> fin_cases j
  · change AnalyticAt ℝ (fun x : P => (-η : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (η : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*r x)+(0)*(-η) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*r x)+(0)*((-η)+(η)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*(q x+r x))+(0)*(-η) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*(q x+r x))+(0)*((-η)+(η)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (2*r x : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (2*p x : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((-η)+(0)*(2*r x) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((-η)+(0)*((2*r x)+(2*p x)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((0)+(0)*(2*r x) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((0)+(0)*((2*r x)+(2*p x)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (2*(p x+r x) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (η : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((0)+(0)*(2*(p x+r x)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((0)+(0)*((2*(p x+r x))+(η)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*q x)+(0)*(2*(p x+r x)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*q x)+(0)*((2*(p x+r x))+(η)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (2*p x : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*(q x+r x))+(0)*(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*(q x+r x))+(0)*((0)+(2*p x)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*(q x+r x)+η)+(0)*(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*(q x+r x)+η)+(0)*((0)+(2*p x)) : ℝ)) x₀
    fun_prop


theorem diagonalTrapezoid2_analytic (r : P → ℝ) (η : ℝ) (x₀ : P)
    (hr : AnalyticAt ℝ r x₀) (i : Fin 2) (j : Fin 6) :
    AnalyticAt ℝ (fun x => (diagonalTrapezoid2 (r x) η i).coordinate j) x₀ := by
  fin_cases i <;> fin_cases j
  · change AnalyticAt ℝ (fun x : P => (-η : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (η : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((0)+(1)*(-η) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((0)+(1)*((-η)+(η)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*r x)+(0)*(-η) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*r x)+(0)*((-η)+(η)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (0 : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => (η : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((0)+(0)*(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((0)+(0)*((0)+(η)) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*r x)+(1)*(0) : ℝ)) x₀
    fun_prop
  · change AnalyticAt ℝ (fun x : P => ((2*r x)+(1)*((0)+(η)) : ℝ)) x₀
    fun_prop


theorem negative_diagonal_trapezoid (R : ℝ) (u d : P → Fin 3 → ℝ)
    (a b : P → ℝ) (T : P → Trapezoid) (τ : P → ℝ) (x₀ : P)
    (hu : ∀ i,AnalyticAt ℝ (fun x => u x i) x₀)
    (hd : ∀ i,AnalyticAt ℝ (fun x => d x i) x₀)
    (ha : AnalyticAt ℝ a x₀) (hb : AnalyticAt ℝ b x₀)
    (hT : ∀ i,AnalyticAt ℝ (fun x => (T x).coordinate i) x₀)
    (hτ : AnalyticAt ℝ τ x₀) (hv : (T x₀).Valid) :
    AnalyticAt ℝ (fun x => ∫ y in diagonalEquiv2 (a x) (b x) '' (T x).body,
      4*R^2*affineEval (u x) y+squareNegativePolynomial R (τ x-affineEval (d x) y)) x₀ := by
  have hB (i j : Fin 2) : AnalyticAt ℝ
      (fun _ : P => (!![0,1;1,-1] : PlaneMatrix) i j) x₀ := analyticAt_const
  have hc (i : Fin 2) : AnalyticAt ℝ (fun x => (![a x,b x] : Plane) i) x₀ := by
    fin_cases i
    · exact ha
    · exact hb
  have h := ParameterArea.negative_trapezoid R
    (fun x => affineCompose (u x) !![0,1;1,-1] ![a x,b x])
    (fun x => affineCompose (d x) !![0,1;1,-1] ![a x,b x]) T τ x₀
    (ParameterArea.affine_compose u _ _ x₀ hu hB hc)
    (ParameterArea.affine_compose d _ _ x₀ hd hB hc) hT hτ hv
  simp_rw [affineCompose_eval] at h
  simp_rw [diagonalEquiv2_integral]
  simpa only [diagonalEquiv2_affine] using h

theorem region2_positive_eventually (p q r : P → ℝ) (x₀ : P)
    (hp : AnalyticAt ℝ p x₀) (hq : AnalyticAt ℝ q x₀) (hr : AnalyticAt ℝ r x₀)
    (hp₀ : 0<p x₀) (hq₀ : 0<q x₀) (hr₀ : 0<r x₀) :
    ∀ᶠ x in nhds x₀,0<p x ∧ 0<q x ∧ 0<r x := by
  filter_upwards [hp.continuousAt.eventually_const_lt hp₀,
    hq.continuousAt.eventually_const_lt hq₀,hr.continuousAt.eventually_const_lt hr₀] with x hp hq hr
  exact ⟨hp,hq,hr⟩

end D4.C23Local
