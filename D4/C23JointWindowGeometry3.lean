import D4.C23JointWindowParameters
import D4.C23JointWindowContainment

/-! Uniform embedded eight-site windows under joint parameter variation. -/
noncomputable section
namespace D4.C23Local
open Analytic AreaEnvelope Matrix Set Filter Topology
attribute [local instance] Matrix.normedAddCommGroup

theorem path3_valid_windows_joint (z : Parameters) (hz : ∀ i,0<z i) :
    ∃ η R : ℝ,0<η ∧ 0<R ∧ 2*η≤R ∧
      ∀ᶠ p : Parameters × ℝ in nhds (z,0),
        ValidLocalWindow (form3 (path3 p.1 p.2)) (path3Window p.1 η R p.2) sites3 := by
  obtain ⟨η,R,ε,hη,hR,hηR,hε,hw⟩ :=
    boundary3_rectangleWindow_sites z (fun i => (hz i).le) (fun i _ => hz i)
  have he : ∀ᶠ p : Parameters × ℝ in nhds (z,0),
      ‖form3 (path3 p.1 p.2)-boundary3Form z‖<ε := by
    have hc : ContinuousAt (fun p : Parameters × ℝ => form3 (path3 p.1 p.2)) (z,0) :=
      form3_path3_joint_continuous.continuousAt
    have h := hc.eventually
      (Metric.ball_mem_nhds (form3 (path3 z 0)) hε)
    simpa only [Metric.mem_ball,dist_eq_norm,path3_at_zero] using h
  refine ⟨η/2,R/2,by positivity,by positivity,by linarith,?_⟩
  filter_upwards [path3_posDef_eventually_joint z hz,
    parameters_eventually_close z (show 0<η/4 by positivity),he] with p hp hc hclose
  have hs := hw (form3 (path3 p.1 p.2)) hp hclose
  have hW := moving_window3_subset (form3 (path3 p.1 p.2)) z p.1 hη.le hR.le
    (hc 1).le (hc 2).le
  refine ⟨hp,localWindow3_compact _ (by unfold lower3 min3; fun_prop) _
    isCompact_Icc (R/2),?_,?_⟩
  · intro r hr n hn
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hs.1 r (hW hr) n hn)
    exact ⟨i,hi⟩
  · intro r hr n hn
    exact hs.2 r (hW hr) n (hW hn)

end D4.C23Local
