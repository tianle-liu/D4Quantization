import D4.AreaTrapezoidGeometry

/-! Analytic moving trapezoids give analytic actual polynomial integrals. -/
noncomputable section
namespace D4.AreaEnvelope
open Set Matrix MeasureTheory Filter Topology

def Trapezoid.coordinate (T : Trapezoid) : Fin 6 → ℝ :=
  ![T.left,T.width,T.bottomLeft,T.bottomRight,T.topLeft,T.topRight]

theorem Trapezoid.valid_eventually (T : ℝ → Trapezoid) (t₀ : ℝ)
    (ha : ∀ k,AnalyticAt ℝ (fun t => (T t).coordinate k) t₀) (hT : (T t₀).Valid) :
    ∀ᶠ t in nhds t₀,(T t).Valid := by
  have h1 := (ha 1).continuousAt.eventually_const_lt hT.1
  have h2 := ((ha 4).sub (ha 2)).continuousAt.eventually_const_lt (sub_pos.mpr hT.2.1)
  have h3 := ((ha 5).sub (ha 3)).continuousAt.eventually_const_lt (sub_pos.mpr hT.2.2)
  filter_upwards [h1,h2,h3] with t ht1 ht2 ht3
  exact ⟨ht1,by change 0<(T t).topLeft-(T t).bottomLeft at ht2; linarith,
    by change 0<(T t).topRight-(T t).bottomRight at ht3; linarith⟩

theorem Trapezoid.matrix_analytic (T : ℝ → Trapezoid) (t₀ : ℝ)
    (ha : ∀ k,AnalyticAt ℝ (fun t => (T t).coordinate k) t₀) (i j k : Fin 2) :
    AnalyticAt ℝ (fun t => (T t).matrix i j k) t₀ := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact ha 1
  · exact ha 1
  · exact (ha 3).sub (ha 2)
  · exact (ha 5).sub (ha 2)
  · exact ha 1
  · exact analyticAt_const
  · exact (ha 5).sub (ha 2)
  · exact (ha 4).sub (ha 2)

theorem Trapezoid.origin_analytic (T : ℝ → Trapezoid) (t₀ : ℝ)
    (ha : ∀ k,AnalyticAt ℝ (fun t => (T t).coordinate k) t₀) (i : Fin 2) :
    AnalyticAt ℝ (fun t => (T t).origin i) t₀ := by
  fin_cases i
  · exact ha 0
  · exact ha 2

theorem analyticAt_negativeTrapezoidIntegral (R : ℝ) (u d : ℝ → Fin 3 → ℝ)
    (T : ℝ → Trapezoid) (t₀ : ℝ)
    (hu : ∀ i,AnalyticAt ℝ (fun t => u t i) t₀)
    (hd : ∀ i,AnalyticAt ℝ (fun t => d t i) t₀)
    (hT : ∀ k,AnalyticAt ℝ (fun t => (T t).coordinate k) t₀)
    (hvalid : (T t₀).Valid) :
    AnalyticAt ℝ (fun t => ∫ x in (T t).body,
      4*R^2*affineEval (u t) x+squareNegativePolynomial R (t-affineEval (d t) x)) t₀ := by
  have ha (i : Fin 2) := analyticAt_negativeTriangleIntegral R u d
    (fun t => (T t).matrix i) (fun t => (T t).origin) t₀ hu hd
    (Trapezoid.matrix_analytic T t₀ hT i) (Trapezoid.origin_analytic T t₀ hT)
    ((T t₀).matrix_det_pos hvalid i).ne'
  apply (Finset.analyticAt_sum Finset.univ fun i _ => ha i).congr
  filter_upwards [Trapezoid.valid_eventually T t₀ hT hvalid] with t ht
  apply ((T t).integral_triangles ht _ ?_).symm
  unfold squareNegativePolynomial
  have hcu := affineEval_continuous (u t)
  have hcd := affineEval_continuous (d t)
  exact (by fun_prop : Continuous (fun x =>
    4*R^2*affineEval (u t) x+(-2*R^3+R^2*(t-affineEval (d t) x)-
      R*(t-affineEval (d t) x)^2+(t-affineEval (d t) x)^3/6))).continuousOn

end D4.AreaEnvelope
