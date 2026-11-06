import D4.Definitions
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! Exact cube integrals used by the parity-lattice quantizer. -/
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace D4.Analytic

/-- In the coordinate supremum norm this is the centered unit cube. -/
def centeredCube : Set Vec := closedBall 0 (1/2)

theorem centeredCube_volume : volume centeredCube = 1 := by
  rw [centeredCube, Real.volume_pi_closedBall _ (by norm_num)]
  norm_num

theorem centeredCube_norm_tail {t : ℝ} (ht : 0 < t) (htop : t ≤ 1/2) :
    (volume.restrict centeredCube).real {x : Vec | t ≤ ‖x‖} = 1 - (2*t)^4 := by
  have hs : MeasurableSet {x : Vec | t ≤ ‖x‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hset : {x : Vec | t ≤ ‖x‖} ∩ centeredCube = centeredCube \ ball 0 t := by
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, mem_diff, mem_ball, dist_zero_right, not_lt]
    exact and_comm
  have hb : ball (0 : Vec) t ⊆ centeredCube := by
    intro x hx
    exact (mem_closedBall.mpr ((mem_ball.mp hx).le.trans htop))
  have hf : volume (ball (0 : Vec) t) ≠ ∞ := by
    rw [Real.volume_pi_ball _ ht]
    exact ENNReal.ofReal_ne_top
  rw [measureReal_def, Measure.restrict_apply hs, hset,
    measure_diff hb measurableSet_ball.nullMeasurableSet hf,
    ENNReal.toReal_sub_of_le (measure_mono hb) (by rw [centeredCube_volume]; simp),
    centeredCube_volume, Real.volume_pi_ball _ ht]
  simp only [ENNReal.toReal_one, Fintype.card_fin, ENNReal.toReal_ofReal (by positivity :
    0 ≤ (2*t)^4)]

/-- The expected largest absolute rounding residual in four dimensions. -/
theorem integral_norm_centeredCube : (∫ x in centeredCube, ‖x‖) = 2/5 := by
  have hi : IntegrableOn (fun x : Vec => ‖x‖) centeredCube :=
    continuous_norm.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hn : (0 : Vec → ℝ) ≤ᵐ[volume.restrict centeredCube] (fun x => ‖x‖) :=
    Filter.Eventually.of_forall (fun x => norm_nonneg x)
  have hb : (fun x : Vec => ‖x‖) ≤ᵐ[volume.restrict centeredCube] (fun _ => (1/2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    simpa only [centeredCube, mem_closedBall, dist_zero_right] using hx
  rw [hi.integral_eq_integral_Ioc_meas_le hn hb]
  calc
    (∫ t in Ioc (0 : ℝ) (1/2), (volume.restrict centeredCube).real {x : Vec | t ≤ ‖x‖}) =
        ∫ t in Ioc (0 : ℝ) (1/2), (1-(2*t)^4) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      exact centeredCube_norm_tail ht.1 ht.2
    _ = ∫ t in (0 : ℝ)..(1/2), (1-(2*t)^4) :=
      (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1/2)).symm
    _ = 2/5 := by
      have he : (fun t : ℝ => 1-(2*t)^4) = fun t => 1-16*t^4 := by
        funext t
        ring
      have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 (1/2) :=
        intervalIntegrable_const
      have hp : IntervalIntegrable (fun t : ℝ => (16 : ℝ)*t^4) volume 0 (1/2) :=
        (show Continuous (fun t : ℝ => (16 : ℝ)*t^4) from
          continuous_const.mul (continuous_id.pow 4)).intervalIntegrable _ _
      rw [he, intervalIntegral.integral_sub hc hp,
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_pow]
      norm_num

end D4.Analytic
