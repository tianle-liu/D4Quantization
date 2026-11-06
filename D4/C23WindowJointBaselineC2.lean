import D4.C23WindowJointQuadraticC2
import D4.C23JointC2Negative
import D4.C23JointPaths
import D4.C23PathLocalIntegrals

/-! Joint analyticity of the actual C2 window baseline, allowing every
tangential parameter and the transverse parameter to vary together. -/
noncomputable section
namespace D4.C23Local
open Matrix MeasureTheory Set Analytic AreaEnvelope

theorem path2LocalBaseline_joint_analytic (z : Parameters) (hz : ∀i,0<z i)
    (η R : ℝ) (hη : 0<η) :
    AnalyticAt ℝ (fun x : Parameters×ℝ => path2LocalBaseline x.1 η R x.2) (z,0) :=
  negativeAreaIntegral2_joint_analytic
    (fun x : Parameters×ℝ => x.1 3) (fun x => x.1 4) (fun x => x.1 9)
    (fun x => 2*x.2) η R (z,0)
    (Joint.coordinate_analytic (z,0) 3) (Joint.coordinate_analytic (z,0) 4)
    (Joint.coordinate_analytic (z,0) 9) (analyticAt_const.mul analyticAt_snd)
    (hz 3) (hz 4) (hz 9) hη

theorem path2WindowBaseline_joint_analytic (z : Parameters) (hz : ∀i,0<z i)
    (η R : ℝ) (hη : 0<η) :
    AnalyticAt ℝ (fun x : Parameters×ℝ => path2WindowBaseline x.1 η R x.2) (z,0) := by
  have hQ : (form2 (path2 z 0)).PosDef := by
    rw [path2_at_zero]
    exact boundary2_posDef z (fun i => (hz i).le) (fun i _ => hz i)
  have hform := Joint.form2_analytic (fun x : Parameters×ℝ => path2 x.1 x.2)
    (z,0) (Joint.path2_analytic (z,0))
  have hquad := localWindow2_quadratic_joint_moving
    (fun x : Parameters×ℝ => form2 (path2 x.1 x.2))
    (fun x : Parameters×ℝ => (form2 (path2 x.1 x.2))⁻¹)
    (fun x : Parameters×ℝ => x.1 3) (fun x => x.1 4) (fun x => x.1 9)
    η R (z,0) hform (ParameterAnalytic.matrix_inv _ (z,0) hform hQ.det_pos.ne')
    (Joint.coordinate_analytic (z,0) 3) (Joint.coordinate_analytic (z,0) 4)
    (Joint.coordinate_analytic (z,0) 9) (hz 3) (hz 4) (hz 9) hη
  have hquad4 : AnalyticAt ℝ (fun x : Parameters×ℝ =>
      ∫r in path2Window x.1 η R x.2,quadratic (form2 (path2 x.1 x.2))⁻¹ r/4) (z,0) := by
    simpa only [path2Window,integral_div] using
      hquad.div (analyticAt_const : AnalyticAt ℝ (fun _ : Parameters×ℝ => (4:ℝ)) (z,0)) (by norm_num)
  exact (analyticAt_const.mul hquad4).add (path2LocalBaseline_joint_analytic z hz η R hη)

end D4.C23Local
