import D4.C23LocalContinuationC3
import D4.C23LocalAnalyticC2
import D4.C23PathPolynomials

/-! Actual local area integrals on fixed neighborhoods, with exactly the
same corrections as the independently verified global path polynomials. -/
noncomputable section
namespace D4.C23Local
open Set MeasureTheory Filter Topology AreaEnvelope

def path2LocalBaseline (z : Parameters) (η R a : ℝ) : ℝ :=
  negativeAreaIntegral {L : Plane | gap2 (z 3) (z 4) (z 9) L≤η}
    R (lower2 (z 9)) (gap2 (z 3) (z 4) (z 9)) (2*a)

def path3LocalBaseline (z : Parameters) (η R b : ℝ) : ℝ :=
  negativeAreaIntegral (localRectangle3 (2*z 1) (2*z 2) η η)
    R lower3 (gap3 (2*z 1-2*b) (2*z 2-2*b)) (2*b)

theorem path2LocalBaseline_analytic (z : Parameters) (η R a₀ : ℝ)
    (h3 : 0≤z 3) (h4 : 0≤z 4) (h9 : 0≤z 9) (hη : 0≤η) :
    AnalyticAt ℝ (path2LocalBaseline z η R) a₀ :=
  correction2_negative_analytic (z 3) (z 4) (z 9) η R a₀ h3 h4 h9 hη

theorem path3LocalBaseline_analytic (z : Parameters) (η R : ℝ)
    (h1 : 0<z 1) (h2 : 0<z 2) (hη : 0<η) :
    AnalyticAt ℝ (path3LocalBaseline z η R) 0 :=
  correction3_negative_rectangle_analytic_parameter (z 1) (z 2) η R h1 h2 hη

theorem path2_local_correction (z : Parameters) (η R : ℝ)
    (h3 : 0≤z 3) (h4 : 0≤z 4) (h9 : 0≤z 9) (hη : 0<η) (hR : 2*η≤R) :
    ∀ᶠ a : ℝ in nhds 0,
      areaIntegral {L : Plane | gap2 (z 3) (z 4) (z 9) L≤η}
        R (lower2 (z 9)) (gap2 (z 3) (z 4) (z 9)) (2*a)=
      path2LocalBaseline z η R a+path2Correction z a := by
  have htw : ContinuousAt (fun a : ℝ => 2*a) 0 := by fun_prop
  filter_upwards [htw.eventually_const_lt (show -η<2*(0:ℝ) by linarith),
    htw.eventually_lt_const (show 2*(0:ℝ)<η by linarith)] with a hlo hhi
  by_cases ha : 0≤a
  · rw [path2Correction,if_pos ha]
    have h := correction2_actual (z 3) (z 4) (z 9) a η R h3 h4 h9 ha hhi.le (by linarith)
    change _-path2LocalBaseline z η R a=_ at h
    linarith
  · rw [path2Correction,if_neg ha,add_zero]
    change areaIntegral _ _ _ _ _=negativeAreaIntegral _ _ _ _ _
    have hU : Continuous (lower2 (z 9)) := by unfold lower2 min4; fun_prop
    apply areaIntegral_eq_negative_of_nonpos _
      (gap2_sublevel_compact (z 3) (z 4) (z 9) η h3 h4 h9 hη.le)
      R (by linarith) _ _ hU.continuousOn (gap2_continuous _ _ _).continuousOn
      (fun L _ => gap2_nonneg _ _ _ L) (2*a) (by linarith)
    intro L hL
    have hn := gap2_nonneg (z 3) (z 4) (z 9) L
    change gap2 (z 3) (z 4) (z 9) L≤η at hL
    apply abs_le.mpr
    constructor <;> linarith

theorem path3_local_correction (z : Parameters) (η R : ℝ)
    (h1 : 0<z 1) (h2 : 0<z 2) (hη : 0<η) (hR : 2*η≤R) :
    ∀ᶠ b : ℝ in nhds 0,
      areaIntegral (localRectangle3 (2*z 1) (2*z 2) η η)
        R lower3 (gap3 (2*z 1-2*b) (2*z 2-2*b)) (2*b)=
      path3LocalBaseline z η R b+path3Correction z b := by
  filter_upwards [correction3_actual_rectangle_eventually (z 1) (z 2) η R h1 h2 hη hR] with b hb
  change _=path3LocalBaseline z η R b+_ at hb
  rw [hb]
  congr 1
  by_cases h : 0≤b
  · rw [max_eq_left h,path3Correction,if_pos h]
  · rw [max_eq_right (le_of_lt (lt_of_not_ge h)),path3Correction,if_neg h]
    simp

end D4.C23Local
