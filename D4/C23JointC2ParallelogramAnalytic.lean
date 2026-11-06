import D4.C23JointC2Parallelograms

/-! Joint analytic integrals on all seven genuine parallelogram pieces
of the C2 moving local window. -/
noncomputable section
namespace D4.C23Local
open Analytic AreaEnvelope Matrix MeasureTheory Set Filter Topology
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem centralRegion2_window_quadratic_analytic
    (Q H : P → Gram) (p q r : P → ℝ) (u : P → Fin 3 → ℝ)
    (R : ℝ) (x₀ : P) (i : Fin 3)
    (hQ : ∀ a b,AnalyticAt ℝ (fun x => Q x a b) x₀)
    (hH : ∀ a b,AnalyticAt ℝ (fun x => H x a b) x₀)
    (hp : AnalyticAt ℝ p x₀) (hq : AnalyticAt ℝ q x₀) (hr : AnalyticAt ℝ r x₀)
    (hu : ∀ a,AnalyticAt ℝ (fun x => u x a) x₀)
    (hp₀ : 0<p x₀) (hq₀ : 0<q x₀) (hr₀ : 0<r x₀) :
    AnalyticAt ℝ (fun x => ∫ v in localWindow2 (Q x) (affineEval (u x))
      (centralRegion2 (p x) (q x) (r x) i) R,quadratic (H x) v) x₀ := by
  have hB : ∀ a b,AnalyticAt ℝ
      (fun x => centralMatrix2 (p x) (q x) (r x) i a b) x₀ := by
    intro a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp only [centralMatrix2,stripMatrix,swapPlaneMatrix,Matrix.of_apply,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk] <;> fun_prop
  have hc : ∀ a,AnalyticAt ℝ (fun x => centralOrigin2 (q x) (r x) i a) x₀ := by
    intro a
    fin_cases i <;> fin_cases a <;>
      simp only [centralOrigin2,stripOrigin,swapPlaneOrigin,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk] <;> fun_prop
  have h := localWindow2_affine_quadratic_analytic planeUnitSquare isCompact_Icc R Q H
    (fun x => centralMatrix2 (p x) (q x) (r x) i)
    (fun x => centralOrigin2 (q x) (r x) i) u x₀ hQ hH hB hc hu
    (centralMatrix2_det_ne _ _ _ hp₀ hq₀ hr₀ i)
  apply h.congr
  filter_upwards [hp.continuousAt.eventually_const_lt hp₀,
    hq.continuousAt.eventually_const_lt hq₀,hr.continuousAt.eventually_const_lt hr₀]
    with x hpx hqx hrx
  rw [centralRegion2_affine_square _ _ _ hpx hqx hrx]

theorem rectangularRegion2_window_quadratic_analytic
    (Q H : P → Gram) (p q r : P → ℝ) (u : P → Fin 3 → ℝ)
    (η R : ℝ) (x₀ : P) (i : Fin 4)
    (hQ : ∀ a b,AnalyticAt ℝ (fun x => Q x a b) x₀)
    (hH : ∀ a b,AnalyticAt ℝ (fun x => H x a b) x₀)
    (hp : AnalyticAt ℝ p x₀) (hq : AnalyticAt ℝ q x₀) (hr : AnalyticAt ℝ r x₀)
    (hu : ∀ a,AnalyticAt ℝ (fun x => u x a) x₀)
    (hp₀ : 0<p x₀) (hq₀ : 0<q x₀) (hη : 0<η) :
    AnalyticAt ℝ (fun x => ∫ v in localWindow2 (Q x) (affineEval (u x))
      (localRegion2 (p x) (q x) (r x) η (![1,2,4,5] i)) R,quadratic (H x) v) x₀ := by
  have hB : ∀ a b,AnalyticAt ℝ
      (fun x => rectangularMatrix2 (p x) (q x) η i a b) x₀ := by
    intro a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp only [rectangularMatrix2,Matrix.of_apply,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk] <;> fun_prop
  have hc : ∀ a,AnalyticAt ℝ (fun x => rectangularOrigin2 (p x) (q x) (r x) η i a) x₀ := by
    intro a
    fin_cases i <;> fin_cases a <;>
      simp only [rectangularOrigin2,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val,Fin.reduceFinMk] <;> fun_prop
  have h := localWindow2_affine_quadratic_analytic planeUnitSquare isCompact_Icc R Q H
    (fun x => rectangularMatrix2 (p x) (q x) η i)
    (fun x => rectangularOrigin2 (p x) (q x) (r x) η i) u x₀ hQ hH hB hc hu
    (rectangularMatrix2_det_ne _ _ _ hp₀ hq₀ hη i)
  apply h.congr
  filter_upwards [hp.continuousAt.eventually_const_lt hp₀,
    hq.continuousAt.eventually_const_lt hq₀] with x hpx hqx
  rw [rectangularRegion2_affine_square _ _ _ _ hpx hqx hη]

end D4.C23Local
