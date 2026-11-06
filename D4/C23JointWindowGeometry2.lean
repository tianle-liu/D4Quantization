import D4.C23JointWindowParameters
import D4.C23JointWindowContainment

/-! Uniform embedded ten-site windows under joint tangential and transverse
 variation. All localization properties are inherited from a genuine larger
 window around the fixed boundary face. -/
noncomputable section
namespace D4.C23Local
open Analytic AreaEnvelope Matrix Set Filter Topology
attribute [local instance] Matrix.normedAddCommGroup

theorem path2_valid_windows_joint (z : Parameters) (hz : ∀ i,0<z i) :
    ∃ η R : ℝ,0<η ∧ 0<R ∧ 2*η≤R ∧
      ∀ᶠ p : Parameters × ℝ in nhds (z,0),
        ValidLocalWindow (form2 (path2 p.1 p.2)) (path2Window p.1 η R p.2) sites2 := by
  obtain ⟨η,R,ε,hη,hR,hηR,hε,hw⟩ :=
    boundary2_localWindow_sites z (fun i => (hz i).le) (fun i _ => hz i)
  let δ := min (η/16) (R/4)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  have he : ∀ᶠ p : Parameters × ℝ in nhds (z,0),
      ‖form2 (path2 p.1 p.2)-boundary2Form z‖<ε := by
    have hc : ContinuousAt (fun p : Parameters × ℝ => form2 (path2 p.1 p.2)) (z,0) :=
      form2_path2_joint_continuous.continuousAt
    have h := hc.eventually
      (Metric.ball_mem_nhds (form2 (path2 z 0)) hε)
    simpa only [Metric.mem_ball,dist_eq_norm,path2_at_zero] using h
  refine ⟨η/2,R/2,by positivity,by positivity,by linarith,?_⟩
  filter_upwards [path2_posDef_eventually_joint z hz,parameters_eventually_pos z hz,
    parameters_eventually_close z hδ,he] with p hp hpos hc hclose
  have hs := hw (form2 (path2 p.1 p.2)) hp hclose
  have hW := moving_window2_subset (form2 (path2 p.1 p.2)) z p.1
    (min_le_left _ _) (min_le_right _ _) (fun i => (hc i).le)
  refine ⟨hp,localWindow2_compact _ (by unfold lower2 min4; fun_prop) _
    (gap2_sublevel_compact _ _ _ (η/2) (hpos 3).le (hpos 4).le (hpos 9).le
      (by positivity)) (R/2),?_,?_⟩
  · intro r hr n hn
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hs.1 r (hW hr) n hn)
    exact ⟨i,hi⟩
  · intro r hr n hn
    exact hs.2 r (hW hr) n (hW hn)

end D4.C23Local
