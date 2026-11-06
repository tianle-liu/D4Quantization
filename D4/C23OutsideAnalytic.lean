import D4.C23PathWindowGeometry
import D4.C23PathMoments
import D4.DualRemainderAnalytic

/-! Analyticity of the genuine outside integrals across both cone boundaries.
All localization and moment identities are discharged by proved geometry and
independent full Voronoi integrations; no subdivision hypothesis is assumed. -/
noncomputable section
namespace D4.C23Local
open Matrix Set MeasureTheory Analytic

theorem path2_outside_analytic (z : Parameters) (hz : ∀ i,0<z i) (c : Vec) :
    ∃ η R : ℝ,0<η ∧ 0<R ∧ 2*η≤R ∧
      AnalyticAt ℝ (fun a => ∫ r in
        dualRemainder (form2 (path2 z a)) c (path2Window z η R a),
          dualNearest (form2 (path2 z a)) r) 0 := by
  obtain ⟨η,R,hη,hR,hηR,hw⟩ := path2_valid_windows z hz
  refine ⟨η,R,hη,hR,hηR,?_⟩
  apply dualRemainder_analytic_of_matching_correction
    (fun a => form2 (path2 z a)) (path2Window z η R) c 0
    (path2Base z) (path2WindowBaseline z η R) (path2Correction z)
    (path2Base_analytic z 0) (path2WindowBaseline_analytic z hz η R hη.le)
  · exact hw.mono fun a ha => ⟨ha.1,ha.2.1,ha.2.2.2⟩
  · exact path2_moment_eventually z hz
  · exact path2_window_correction z hz η R hη hηR (hw.mono fun a ha => ha.2.2.1)

theorem path3_outside_analytic (z : Parameters) (hz : ∀ i,0<z i) (c : Vec) :
    ∃ η R : ℝ,0<η ∧ 0<R ∧ 2*η≤R ∧
      AnalyticAt ℝ (fun b => ∫ r in
        dualRemainder (form3 (path3 z b)) c (path3Window z η R b),
          dualNearest (form3 (path3 z b)) r) 0 := by
  obtain ⟨η,R,hη,hR,hηR,hw⟩ := path3_valid_windows z hz
  refine ⟨η,R,hη,hR,hηR,?_⟩
  apply dualRemainder_analytic_of_matching_correction
    (fun b => form3 (path3 z b)) (path3Window z η R) c 0
    (path3Base z) (path3WindowBaseline z η R) (path3Correction z)
    (path3Base_analytic z 0) (path3WindowBaseline_analytic z hz η R hη)
  · exact hw.mono fun b hb => ⟨hb.1,hb.2.1,hb.2.2.2⟩
  · exact path3_moment_eventually z hz
  · exact path3_window_correction z hz η R hη hηR (hw.mono fun b hb => hb.2.2.1)

end D4.C23Local
