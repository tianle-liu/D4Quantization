import D4.C23LocalAnalyticC3
import D4.C23LocalRectangleNeighborhood

/-! The actual fixed-window integral has an analytic baseline and precisely
the positive-side correction in the paper, on a two-sided neighborhood. -/
noncomputable section
namespace D4.C23Local
open Set MeasureTheory Filter Topology AreaEnvelope

theorem correction3_negative_rectangle_analytic_parameter (u v η R : ℝ)
    (hu : 0<u) (hv : 0<v) (hη : 0<η) :
    AnalyticAt ℝ (fun b => negativeAreaIntegral (localRectangle3 (2*u) (2*v) η η)
      R lower3 (gap3 (2*u-2*b) (2*v-2*b)) (2*b)) 0 := by
  have h := correction3_negative_rectangle_analytic (2*u) (2*v) η R
    (by positivity) (by positivity) hη
  exact h.comp_of_eq (by fun_prop : AnalyticAt ℝ (fun b : ℝ => 2*b) 0) (by ring)

theorem correction3_actual_rectangle_eventually (u v η R : ℝ)
    (hu : 0<u) (hv : 0<v) (hη : 0<η) (hR : 2*η≤R) :
    ∀ᶠ b : ℝ in nhds 0,
    areaIntegral (localRectangle3 (2*u) (2*v) η η) R lower3
      (gap3 (2*u-2*b) (2*v-2*b)) (2*b) =
    negativeAreaIntegral (localRectangle3 (2*u) (2*v) η η) R lower3
      (gap3 (2*u-2*b) (2*v-2*b)) (2*b) +
      2*(max b 0)^3*(3*(max b 0)^2-5*(max b 0)*(u+v)+10*u*v) := by
  have htw : ContinuousAt (fun b : ℝ => 2*b) 0 := by fun_prop
  have hid : ContinuousAt (fun b : ℝ => b) 0 := continuousAt_id
  filter_upwards [htw.eventually_const_lt (show -η<2*(0:ℝ) by linarith),
    htw.eventually_lt_const (show 2*(0:ℝ)<η by linarith),
    hid.eventually_lt_const hu,hid.eventually_lt_const hv] with b hlo hhi hbu hbv
  by_cases hb : 0≤b
  · rw [max_eq_left hb]
    have h := correction3_actual_rectangle u v b η R hb hbu.le hbv.le hhi.le hR
    linarith
  · have hb0 : b≤0 := le_of_lt (lt_of_not_ge hb)
    rw [max_eq_right hb0]
    simp only [zero_pow (by decide : 3≠0),mul_zero,zero_mul,add_zero]
    exact correction3_rectangle_nonpos (2*u) (2*v) η R (2*b) hη.le hlo.le
      (by linarith) hR

end D4.C23Local
