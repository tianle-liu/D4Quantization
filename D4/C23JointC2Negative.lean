import D4.C23JointC2AnalyticPieces

/-! Joint analyticity of the actual C2 negative local integral, with all
three positive tangential parameters and the transverse variable varying. -/
noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope Filter Topology
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem region2_negative_integral_analytic (p q r τ : P → ℝ) (η R : ℝ) (x₀ : P)
    (hp : AnalyticAt ℝ p x₀) (hq : AnalyticAt ℝ q x₀) (hr : AnalyticAt ℝ r x₀)
    (hτ : AnalyticAt ℝ τ x₀) (hp₀ : 0<p x₀) (hq₀ : 0<q x₀) (hr₀ : 0<r x₀)
    (hη : 0<η) (i : Fin 9) :
    AnalyticAt ℝ (fun x => ∫ y in localRegion2 (p x) (q x) (r x) η i,
      4*R^2*affineEval (localLower2 (r x) i) y+
        squareNegativePolynomial R (τ x-affineEval (localDistance2 (p x) (q x) (r x) i) y)) x₀ := by
  have hpos := region2_positive_eventually p q r x₀ hp hq hr hp₀ hq₀ hr₀
  fin_cases i
  · have ha : AnalyticAt ℝ (fun x => 4*(p x*q x+p x*r x+q x*r x)*
        squareNegativePolynomial R (τ x)) x₀ := by
      unfold squareNegativePolynomial
      simp only [div_eq_mul_inv]
      fun_prop
    apply ha.congr
    filter_upwards [hpos] with x hx
    simp only [localLower2,localDistance2,localUpper2,Matrix.cons_val_zero,affineEval_eq,
      Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk,zero_mul,zero_add,add_zero,
      neg_zero,sub_zero,setIntegral_const,smul_eq_mul]
    rw [centralRegion2_area _ _ _ _ hx.1.le hx.2.1.le hx.2.2.le]
    simp only [mul_zero, zero_add]
  · have ha := ParameterArea.negative_trapezoid R (fun x => localLower2 (r x) 1) (fun x => localDistance2 (p x) (q x) (r x) 1)
      (fun x => rectangularTrapezoid2 (p x) (q x) (r x) η 0) τ x₀
      (localLower2_analytic r x₀ hr 1) (localDistance2_analytic p q r x₀ hp hq hr 1)
      (rectangularTrapezoid2_analytic p q r η x₀ hp hq hr 0) hτ
      (rectangularTrapezoid2_valid _ _ _ _ hp₀ hq₀ hη 0)
    apply ha.congr
    filter_upwards [hpos] with x hx
    have he := rectangularRegion2_eq (p x) (q x) (r x) η hx.1 hη 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] at he
    rw [←he]
    rfl
  · have ha := ParameterArea.negative_trapezoid R (fun x => localLower2 (r x) 2) (fun x => localDistance2 (p x) (q x) (r x) 2)
      (fun x => rectangularTrapezoid2 (p x) (q x) (r x) η 1) τ x₀
      (localLower2_analytic r x₀ hr 2) (localDistance2_analytic p q r x₀ hp hq hr 2)
      (rectangularTrapezoid2_analytic p q r η x₀ hp hq hr 1) hτ
      (rectangularTrapezoid2_valid _ _ _ _ hp₀ hq₀ hη 1)
    apply ha.congr
    filter_upwards [hpos] with x hx
    have he := rectangularRegion2_eq (p x) (q x) (r x) η hx.1 hη 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] at he
    rw [←he]
    rfl
  · have ha := negative_diagonal_trapezoid R (fun x => localLower2 (r x) 3) (fun x => localDistance2 (p x) (q x) (r x) 3)
      (fun _ : P => 0) (fun x => 2*r x) (fun x => diagonalTrapezoid2 (r x) η 0) τ x₀
      (localLower2_analytic r x₀ hr 3) (localDistance2_analytic p q r x₀ hp hq hr 3) (by fun_prop) (by fun_prop)
      (diagonalTrapezoid2_analytic r η x₀ hr 0) hτ
      (diagonalTrapezoid2_valid _ _ hr₀ hη 0)
    apply ha.congr
    filter_upwards [hpos] with x hx
    have he := diagonalRegion2_eq (p x) (q x) (r x) η hη 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk, diagonalOffset2] at he
    rw [←he]
    rfl
  · have ha := ParameterArea.negative_trapezoid R (fun x => localLower2 (r x) 4) (fun x => localDistance2 (p x) (q x) (r x) 4)
      (fun x => rectangularTrapezoid2 (p x) (q x) (r x) η 2) τ x₀
      (localLower2_analytic r x₀ hr 4) (localDistance2_analytic p q r x₀ hp hq hr 4)
      (rectangularTrapezoid2_analytic p q r η x₀ hp hq hr 2) hτ
      (rectangularTrapezoid2_valid _ _ _ _ hp₀ hq₀ hη 2)
    apply ha.congr
    filter_upwards [hpos] with x hx
    have he := rectangularRegion2_eq (p x) (q x) (r x) η hx.1 hη 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] at he
    rw [←he]
    rfl
  · have ha := ParameterArea.negative_trapezoid R (fun x => localLower2 (r x) 5) (fun x => localDistance2 (p x) (q x) (r x) 5)
      (fun x => rectangularTrapezoid2 (p x) (q x) (r x) η 3) τ x₀
      (localLower2_analytic r x₀ hr 5) (localDistance2_analytic p q r x₀ hp hq hr 5)
      (rectangularTrapezoid2_analytic p q r η x₀ hp hq hr 3) hτ
      (rectangularTrapezoid2_valid _ _ _ _ hp₀ hq₀ hη 3)
    apply ha.congr
    filter_upwards [hpos] with x hx
    have he := rectangularRegion2_eq (p x) (q x) (r x) η hx.1 hη 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] at he
    rw [←he]
    rfl
  · have ha := negative_diagonal_trapezoid R (fun x => localLower2 (r x) 6) (fun x => localDistance2 (p x) (q x) (r x) 6)
      (fun x => 2*p x) (fun x => 2*(q x+r x)) (fun x => diagonalTrapezoid2 (r x) η 1) τ x₀
      (localLower2_analytic r x₀ hr 6) (localDistance2_analytic p q r x₀ hp hq hr 6) (by fun_prop) (by fun_prop)
      (diagonalTrapezoid2_analytic r η x₀ hr 1) hτ
      (diagonalTrapezoid2_valid _ _ hr₀ hη 1)
    apply ha.congr
    filter_upwards [hpos] with x hx
    have he := diagonalRegion2_eq (p x) (q x) (r x) η hη 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk, diagonalOffset2] at he
    rw [←he]
    rfl
  · have hc (j : Fin 2) : AnalyticAt ℝ
        (fun x => cornerOrigin2 (p x) (q x) (r x) 0 j) x₀ := by
      fin_cases j <;> dsimp [cornerOrigin2] <;> fun_prop
    have ha := ParameterArea.negative_triangle R (fun x => localLower2 (r x) 7) (fun x => localDistance2 (p x) (q x) (r x) 7)
      (fun _ : P => cornerMatrix2 η 0) (fun x => cornerOrigin2 (p x) (q x) (r x) 0) τ x₀
      (localLower2_analytic r x₀ hr 7) (localDistance2_analytic p q r x₀ hp hq hr 7) (fun _ _ => analyticAt_const) hc hτ
      (by rw [cornerMatrix2_det]; exact neg_ne_zero.mpr (pow_ne_zero 2 hη.ne'))
    apply ha.congr
    apply Eventually.of_forall
    intro x
    have he := cornerRegion2_eq (p x) (q x) (r x) η hη 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] at he
    dsimp only
    rw [←he]
    rfl
  · have hc (j : Fin 2) : AnalyticAt ℝ
        (fun x => cornerOrigin2 (p x) (q x) (r x) 1 j) x₀ := by
      fin_cases j <;> dsimp [cornerOrigin2] <;> fun_prop
    have ha := ParameterArea.negative_triangle R (fun x => localLower2 (r x) 8) (fun x => localDistance2 (p x) (q x) (r x) 8)
      (fun _ : P => cornerMatrix2 η 1) (fun x => cornerOrigin2 (p x) (q x) (r x) 1) τ x₀
      (localLower2_analytic r x₀ hr 8) (localDistance2_analytic p q r x₀ hp hq hr 8) (fun _ _ => analyticAt_const) hc hτ
      (by rw [cornerMatrix2_det]; exact neg_ne_zero.mpr (pow_ne_zero 2 hη.ne'))
    apply ha.congr
    apply Eventually.of_forall
    intro x
    have he := cornerRegion2_eq (p x) (q x) (r x) η hη 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] at he
    dsimp only
    rw [←he]
    rfl

theorem negativeAreaIntegral2_joint_analytic (p q r τ : P → ℝ) (η R : ℝ) (x₀ : P)
    (hp : AnalyticAt ℝ p x₀) (hq : AnalyticAt ℝ q x₀) (hr : AnalyticAt ℝ r x₀)
    (hτ : AnalyticAt ℝ τ x₀) (hp₀ : 0<p x₀) (hq₀ : 0<q x₀) (hr₀ : 0<r x₀)
    (hη : 0<η) :
    AnalyticAt ℝ (fun x => negativeAreaIntegral {L | gap2 (p x) (q x) (r x) L≤η}
      R (lower2 (r x)) (gap2 (p x) (q x) (r x)) (τ x)) x₀ := by
  have ha (i : Fin 9) := region2_negative_integral_analytic p q r τ η R x₀
    hp hq hr hτ hp₀ hq₀ hr₀ hη i
  have hconst : AnalyticAt ℝ (fun _ : P => (15/4 : ℝ)) x₀ := analyticAt_const
  apply (hconst.mul (Finset.analyticAt_sum Finset.univ fun i _ => ha i)).congr
  filter_upwards [region2_positive_eventually p q r x₀ hp hq hr hp₀ hq₀ hr₀] with x hx
  unfold negativeAreaIntegral
  simp only [Pi.mul_apply]
  congr 1
  rw [localRegion2_integral _ _ _ _ hx.1 hx.2.1 hx.2.2.le hη.le _ (by
    simp only [gap2, lower2, upper2, min4, squareNegativePolynomial]
    fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun (localRegion2_compact _ _ _ _ hx.1.le hx.2.1.le hx.2.2.le hη.le i).measurableSet
  intro y hy
  have hh := localRegion2_affine _ _ _ _ hx.1.le hx.2.1.le hx.2.2.le i y hy
  dsimp only
  rw [localDistance2_eval,← hh.1,← hh.2]
  rfl

end D4.C23Local
