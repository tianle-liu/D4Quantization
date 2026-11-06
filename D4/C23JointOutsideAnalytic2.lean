import D4.C23WindowJointBaselineC2
import D4.C23JointWindowGeometry2
import D4.C23JointLocalCorrection
import D4.C23JointMoments
import D4.DualRemainderJointAnalytic

/-! Joint real analyticity of the genuine outside integral at the principal/C2 wall. -/
noncomputable section
namespace D4.C23Local
open Matrix Set MeasureTheory Analytic

theorem path2_outside_joint_analytic (z : Parameters) (hz : ∀ i,0<z i) (c : Vec) :
    ∃ η R : ℝ,0<η ∧ 0<R ∧ 2*η≤R ∧
      AnalyticAt ℝ (fun p : Parameters×ℝ => ∫ r in
        dualRemainder (form2 (path2 p.1 p.2)) c (path2Window p.1 η R p.2),
          dualNearest (form2 (path2 p.1 p.2)) r) (z,0) := by
  obtain ⟨η,R,hη,hR,hηR,hw⟩ := path2_valid_windows_joint z hz
  refine ⟨η,R,hη,hR,hηR,?_⟩
  apply dualRemainder_joint_analytic_of_matching_correction
    (fun p : Parameters×ℝ => form2 (path2 p.1 p.2))
    (fun p : Parameters×ℝ => path2Window p.1 η R p.2) c (z,0)
    (fun p => path2Base p.1 p.2) (fun p => path2WindowBaseline p.1 η R p.2)
    (fun p => path2Correction p.1 p.2)
    (Joint.path2Base_analytic (z,0)) (path2WindowBaseline_joint_analytic z hz η R hη)
  · exact hw.mono fun p hp => ⟨hp.1,hp.2.1,hp.2.2.2⟩
  · exact Joint.path2_moment_eventually z hz
  · exact path2_window_correction_joint z hz η R hη hηR (hw.mono fun p hp => hp.2.2.1)

end D4.C23Local
