import D4.C23JointC2OuterQuadratic
import D4.C23JointC2ParallelogramAnalytic

noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope Analytic Filter Topology
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem centralHexagon2_window_quadratic_analytic
    (Q H : P → Gram) (p q r : P → ℝ) (u : P → Fin 3 → ℝ)
    (η R : ℝ) (x₀ : P)
    (hQ : ∀i j,AnalyticAt ℝ (fun x => Q x i j) x₀)
    (hH : ∀i j,AnalyticAt ℝ (fun x => H x i j) x₀)
    (hp : AnalyticAt ℝ p x₀) (hq : AnalyticAt ℝ q x₀) (hr : AnalyticAt ℝ r x₀)
    (hu : ∀i,AnalyticAt ℝ (fun x => u x i) x₀)
    (hp₀ : 0<p x₀) (hq₀ : 0<q x₀) (hr₀ : 0<r x₀) (hη : 0≤η) :
    AnalyticAt ℝ (fun x => ∫y in localWindow2 (Q x) (affineEval (u x))
      (localRegion2 (p x) (q x) (r x) η 0) R,quadratic (H x) y) x₀ := by
  have ha (i : Fin 3) := centralRegion2_window_quadratic_analytic
    Q H p q r u R x₀ i hQ hH hp hq hr hu hp₀ hq₀ hr₀
  apply (Finset.analyticAt_sum Finset.univ fun i _ => ha i).congr
  filter_upwards [region2_positive_eventually p q r x₀ hp hq hr hp₀ hq₀ hr₀] with x hx
  have hK (i : Fin 3) : IsCompact (centralRegion2 (p x) (q x) (r x) i) := by
    rw [centralRegion2_affine_square _ _ _ hx.1 hx.2.1 hx.2.2]
    exact isCompact_Icc.image (by unfold Matrix.mulVec dotProduct; fun_prop)
  symm
  exact localWindow2_integral_partition (Q x) (affineEval (u x)) (by
    change Continuous (fun y : Plane => affineEval (u x) y)
    simp_rw [affineEval_eq]; fun_prop)
    _ (localRegion2_compact _ _ _ _ hx.1.le hx.2.1.le hx.2.2.le hη 0)
    _ hK (centralRegion2_cover _ _ _ _ hx.1.le hx.2.1.le hx.2.2.le)
    (centralRegion2_pairwise_null _ _ _) R _ (by unfold quadratic; fun_prop)

theorem region2_window_quadratic_analytic
    (Q H : P → Gram) (p q r : P → ℝ) (η R : ℝ) (x₀ : P)
    (hQ : ∀i j,AnalyticAt ℝ (fun x => Q x i j) x₀)
    (hH : ∀i j,AnalyticAt ℝ (fun x => H x i j) x₀)
    (hp : AnalyticAt ℝ p x₀) (hq : AnalyticAt ℝ q x₀) (hr : AnalyticAt ℝ r x₀)
    (hp₀ : 0<p x₀) (hq₀ : 0<q x₀) (hr₀ : 0<r x₀) (hη : 0<η) (i : Fin 9) :
    AnalyticAt ℝ (fun x => ∫y in localWindow2 (Q x) (affineEval (localLower2 (r x) i))
      (localRegion2 (p x) (q x) (r x) η i) R,quadratic (H x) y) x₀ := by
  fin_cases i
  · exact centralHexagon2_window_quadratic_analytic Q H p q r
      (fun x => localLower2 (r x) 0) η R x₀ hQ hH hp hq hr
      (localLower2_analytic r x₀ hr 0) hp₀ hq₀ hr₀ hη.le
  · exact rectangularRegion2_window_quadratic_analytic Q H p q r
      (fun x => localLower2 (r x) 1) η R x₀ 0 hQ hH hp hq hr
      (localLower2_analytic r x₀ hr 1) hp₀ hq₀ hη
  · exact rectangularRegion2_window_quadratic_analytic Q H p q r
      (fun x => localLower2 (r x) 2) η R x₀ 1 hQ hH hp hq hr
      (localLower2_analytic r x₀ hr 2) hp₀ hq₀ hη
  · exact localWindow2_diagonalRegion_quadratic_analytic p q r η R Q H
      (fun x => localLower2 (r x) 3) x₀ hp hq hr hr₀ hη hQ hH
      (localLower2_analytic r x₀ hr 3) 0
  · exact rectangularRegion2_window_quadratic_analytic Q H p q r
      (fun x => localLower2 (r x) 4) η R x₀ 2 hQ hH hp hq hr
      (localLower2_analytic r x₀ hr 4) hp₀ hq₀ hη
  · exact rectangularRegion2_window_quadratic_analytic Q H p q r
      (fun x => localLower2 (r x) 5) η R x₀ 3 hQ hH hp hq hr
      (localLower2_analytic r x₀ hr 5) hp₀ hq₀ hη
  · exact localWindow2_diagonalRegion_quadratic_analytic p q r η R Q H
      (fun x => localLower2 (r x) 6) x₀ hp hq hr hr₀ hη hQ hH
      (localLower2_analytic r x₀ hr 6) 1
  · exact localWindow2_cornerRegion_quadratic_analytic p q r η R Q H
      (fun x => localLower2 (r x) 7) x₀ hp hq hr hη hQ hH
      (localLower2_analytic r x₀ hr 7) 0
  · exact localWindow2_cornerRegion_quadratic_analytic p q r η R Q H
      (fun x => localLower2 (r x) 8) x₀ hp hq hr hη hQ hH
      (localLower2_analytic r x₀ hr 8) 1

theorem localWindow2_quadratic_joint_moving
    (Q H : P → Gram) (p q r : P → ℝ) (η R : ℝ) (x₀ : P)
    (hQ : ∀i j,AnalyticAt ℝ (fun x => Q x i j) x₀)
    (hH : ∀i j,AnalyticAt ℝ (fun x => H x i j) x₀)
    (hp : AnalyticAt ℝ p x₀) (hq : AnalyticAt ℝ q x₀) (hr : AnalyticAt ℝ r x₀)
    (hp₀ : 0<p x₀) (hq₀ : 0<q x₀) (hr₀ : 0<r x₀) (hη : 0<η) :
    AnalyticAt ℝ (fun x => ∫y in localWindow2 (Q x) (lower2 (r x))
      {L | gap2 (p x) (q x) (r x) L≤η} R,quadratic (H x) y) x₀ := by
  have ha (i : Fin 9) := region2_window_quadratic_analytic Q H p q r η R x₀
    hQ hH hp hq hr hp₀ hq₀ hr₀ hη i
  apply (Finset.analyticAt_sum Finset.univ fun i _ => ha i).congr
  filter_upwards [region2_positive_eventually p q r x₀ hp hq hr hp₀ hq₀ hr₀] with x hx
  symm
  rw [localWindow2_integral_partition (Q x) (lower2 (r x)) (by unfold lower2 min4; fun_prop)
    _ (gap2_sublevel_compact _ _ _ _ hx.1.le hx.2.1.le hx.2.2.le hη.le)
    (localRegion2 (p x) (q x) (r x) η)
    (localRegion2_compact _ _ _ _ hx.1.le hx.2.1.le hx.2.2.le hη.le)
    (localRegion2_union _ _ _ _ hx.1 hx.2.1 hx.2.2.le hη.le)
    (localRegion2_pairwise_null _ _ _ _ hx.1.le hx.2.1.le hx.2.2.le) R
    _ (by unfold quadratic; fun_prop)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [localWindow2_congr_upper (Q x) (lower2 (r x))
    (affineEval (localLower2 (r x) i)) _ R (fun y hy =>
      (localRegion2_affine _ _ _ _ hx.1.le hx.2.1.le hx.2.2.le i y hy).1)]

end D4.C23Local
