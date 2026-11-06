import D4.C23WindowJointBaselineC3
import D4.C23JointWindowGeometry3
import D4.C23JointLocalCorrection
import D4.C23JointMoments
import D4.DualRemainderJointAnalytic

/-! Joint real analyticity of the genuine outside integral at the C2/C3 wall. -/
noncomputable section
namespace D4.C23Local
open Matrix Set MeasureTheory Analytic

theorem path3_outside_joint_analytic (z : Parameters) (hz : ∀ i,0<z i) (c : Vec) :
    ∃ η R : ℝ,0<η ∧ 0<R ∧ 2*η≤R ∧
      AnalyticAt ℝ (fun p : Parameters×ℝ => ∫ r in
        dualRemainder (form3 (path3 p.1 p.2)) c (path3Window p.1 η R p.2),
          dualNearest (form3 (path3 p.1 p.2)) r) (z,0) := by
  obtain ⟨η,R,hη,hR,hηR,hw⟩ := path3_valid_windows_joint z hz
  refine ⟨η,R,hη,hR,hηR,?_⟩
  apply dualRemainder_joint_analytic_of_matching_correction
    (fun p : Parameters×ℝ => form3 (path3 p.1 p.2))
    (fun p : Parameters×ℝ => path3Window p.1 η R p.2) c (z,0)
    (fun p => path3Base p.1 p.2) (fun p => path3WindowBaseline p.1 η R p.2)
    (fun p => path3Correction p.1 p.2)
    (Joint.path3Base_analytic (z,0)) (path3WindowBaseline_joint_analytic z hz η R hη hR)
  · exact hw.mono fun p hp => ⟨hp.1,hp.2.1,hp.2.2.2⟩
  · exact Joint.path3_moment_eventually z hz
  · exact path3_window_correction_joint z hz η R hη hηR (hw.mono fun p hp => hp.2.2.1)

end D4.C23Local
