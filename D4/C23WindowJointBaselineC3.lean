import D4.C23WindowJointQuadratic
import D4.C23LocalJointAnalyticC3
import D4.C23JointPaths
import D4.C23PathLocalIntegrals

noncomputable section
namespace D4.C23Local
open Matrix MeasureTheory Set Analytic AreaEnvelope Principal
attribute [local fun_prop] analyticAt_fst analyticAt_snd

theorem path3LocalBaseline_joint_analytic (z : Parameters) (hz : ∀i,0<z i)
    (η R : ℝ) (hη : 0<η) :
    AnalyticAt ℝ (fun p : Parameters×ℝ=>path3LocalBaseline p.1 η R p.2) (z,0) := by
  have h := correction3_negative_rectangle_joint_analytic (2*z 1) (2*z 2) η R
    (mul_pos (by norm_num) (hz 1)) (mul_pos (by norm_num) (hz 2)) hη
  have hp : AnalyticAt ℝ (fun p : Parameters×ℝ=>(2*p.1 1,2*p.1 2,2*p.2)) (z,0) := by
    apply AnalyticAt.prod
    · exact analyticAt_const.mul (Joint.coordinate_analytic (z,0) 1)
    · apply AnalyticAt.prod
      · exact analyticAt_const.mul (Joint.coordinate_analytic (z,0) 2)
      · exact analyticAt_const.mul analyticAt_snd
  have hh := h.comp_of_eq hp (by simp)
  simpa only [path3LocalBaseline,Function.comp_def,mul_zero] using hh

theorem path3WindowBaseline_joint_analytic (z : Parameters) (hz : ∀i,0<z i)
    (η R : ℝ) (hη : 0<η) (hR : 0<R) :
    AnalyticAt ℝ (fun p : Parameters×ℝ=>path3WindowBaseline p.1 η R p.2) (z,0) := by
  have hQ : (form3 (path3 z 0)).PosDef := by
    rw [path3_at_zero]
    exact boundary3_posDef z (fun i=>(hz i).le) (fun i _=>hz i)
  have hquad := localWindow3_quadratic_joint_moving
    (fun p : Parameters×ℝ=>form3 (path3 p.1 p.2))
    (fun p : Parameters×ℝ=>2*p.1 1) (fun p : Parameters×ℝ=>2*p.1 2)
    η R (z,0) (Joint.form3_analytic _ (z,0) (Joint.path3_analytic (z,0)))
    (analyticAt_const.mul (Joint.coordinate_analytic (z,0) 1))
    (analyticAt_const.mul (Joint.coordinate_analytic (z,0) 2))
    (fun p=>secondary_isHermitian _ _ _) hQ.det_pos.ne'
    (mul_pos (by norm_num) (hz 1)) (mul_pos (by norm_num) (hz 2)) hη hR
  exact (analyticAt_const.mul hquad).add
    (path3LocalBaseline_joint_analytic z hz η R hη)

end D4.C23Local
