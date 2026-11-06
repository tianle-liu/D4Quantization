import D4.C23WindowMeasure
import D4.FixedQuadraticIntegralAnalytic

/-! The common quadratic part of the actual local dual integral is analytic. -/
noncomputable section
namespace D4.C23Local
open Matrix MeasureTheory Set Analytic AreaEnvelope

theorem windowPoint2_shift (Q : Gram) (U : Plane → ℝ) (p : WindowCoordinates) :
    windowPoint2 Q U p=inverseCoordinates2 Q 0+windowPoint2 0 U p := by
  ext i
  fin_cases i <;> norm_num [windowPoint2,inverseCoordinates2,fiberCoordinates,
    Fin.reduceFinMk,Matrix.cons_val] <;> ring

theorem windowPoint3_shift (Q : Gram) (U : Plane → ℝ) (p : WindowCoordinates) :
    windowPoint3 Q U p=inverseCoordinates3 Q 0+windowPoint3 0 U p := by
  ext i
  fin_cases i <;> norm_num [windowPoint3,inverseCoordinates3,fiberCoordinates,
    Fin.reduceFinMk,Matrix.cons_val] <;> ring

theorem localWindow2_quadratic_analytic (Q : ℝ → Gram) (t₀ : ℝ)
    (hQ : ∀ i j, AnalyticAt ℝ (fun t => Q t i j) t₀)
    (hdet : (Q t₀).det ≠ 0) (U : Plane → ℝ) (hU : Continuous U)
    (K : Set Plane) (hK : IsCompact K) (R : ℝ) :
    AnalyticAt ℝ (fun t => ∫ r in localWindow2 (Q t) U K R,
      quadratic (Q t)⁻¹ r/4) t₀ := by
  have he (t : ℝ) : (∫ r in localWindow2 (Q t) U K R,quadratic (Q t)⁻¹ r/4)=
      (∫ p in referenceWindow K R,
        quadratic (Q t)⁻¹ (inverseCoordinates2 (Q t) 0+windowPoint2 0 U p))/4 := by
    rw [localWindow2_integral _ U hU,integral_div]
    congr 1
    apply setIntegral_congr_fun (hK.prod (isCompact_Icc.prod isCompact_Icc)).measurableSet
    intro p _
    exact congrArg (quadratic (Q t)⁻¹) (windowPoint2_shift (Q t) U p)
  simp_rw [he]
  apply AnalyticAt.div _ analyticAt_const (by norm_num : (4:ℝ) ≠ 0)
  apply analyticAt_integral_quadratic_shift (referenceWindow K R)
    (hK.prod (isCompact_Icc.prod isCompact_Icc)) (windowPoint2 0 U)
    (windowPoint2_continuous 0 hU) (fun t => (Q t)⁻¹)
    (fun t => inverseCoordinates2 (Q t) 0) t₀
    (analyticAt_matrix_inv Q t₀ hQ hdet)
  intro i
  fin_cases i <;> norm_num [inverseCoordinates2,Fin.reduceFinMk,Matrix.cons_val]
  · exact hQ 0 0
  · exact hQ 1 1
  · exact (hQ 2 2).neg
  · exact (hQ 3 3).neg

theorem localWindow3_quadratic_analytic (Q : ℝ → Gram) (t₀ : ℝ)
    (hQ : ∀ i j, AnalyticAt ℝ (fun t => Q t i j) t₀)
    (hdet : (Q t₀).det ≠ 0) (U : Plane → ℝ) (hU : Continuous U)
    (K : Set Plane) (hK : IsCompact K) (R : ℝ) :
    AnalyticAt ℝ (fun t => ∫ r in localWindow3 (Q t) U K R,
      quadratic (Q t)⁻¹ r/4) t₀ := by
  have he (t : ℝ) : (∫ r in localWindow3 (Q t) U K R,quadratic (Q t)⁻¹ r/4)=
      (∫ p in referenceWindow K R,
        quadratic (Q t)⁻¹ (inverseCoordinates3 (Q t) 0+windowPoint3 0 U p))/4 := by
    rw [localWindow3_integral _ U hU,integral_div]
    congr 1
    apply setIntegral_congr_fun (hK.prod (isCompact_Icc.prod isCompact_Icc)).measurableSet
    intro p _
    exact congrArg (quadratic (Q t)⁻¹) (windowPoint3_shift (Q t) U p)
  simp_rw [he]
  apply AnalyticAt.div _ analyticAt_const (by norm_num : (4:ℝ) ≠ 0)
  apply analyticAt_integral_quadratic_shift (referenceWindow K R)
    (hK.prod (isCompact_Icc.prod isCompact_Icc)) (windowPoint3 0 U)
    (windowPoint3_continuous 0 hU) (fun t => (Q t)⁻¹)
    (fun t => inverseCoordinates3 (Q t) 0) t₀
    (analyticAt_matrix_inv Q t₀ hQ hdet)
  intro i
  fin_cases i <;> norm_num [inverseCoordinates3,Fin.reduceFinMk,Matrix.cons_val]
  · exact (hQ 0 0).neg
  · exact (hQ 1 1).neg
  · exact hQ 2 2
  · exact hQ 3 3

end D4.C23Local
