import D4.C23PathWindowGeometry2
import D4.C23WindowLocalization

noncomputable section
namespace D4.C23Local
open Matrix Set Analytic AreaEnvelope
attribute [local instance] Matrix.normedAddCommGroup

theorem path3_valid_windows (z : Parameters) (hz : ∀ i,0<z i) :
    ∃ η R : ℝ,0<η ∧ 0<R ∧ 2*η≤R ∧
      ∀ᶠ b in nhds (0:ℝ),ValidLocalWindow (form3 (path3 z b)) (path3Window z η R b) sites3 := by
  obtain ⟨η,R,ε,hη,hR,hηR,hε,hw⟩ :=
    boundary3_rectangleWindow_sites z (fun i => (hz i).le) (fun i _ => hz i)
  have hc : ContinuousAt (fun b => form3 (path3 z b)) 0 :=
    continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
      (form3_analyticAt (path3 z) 0 (path3_analytic z 0) i j).continuousAt
  have he : ∀ᶠ b in nhds (0:ℝ),‖form3 (path3 z b)-boundary3Form z‖<ε := by
    have h := hc.eventually (Metric.ball_mem_nhds (form3 (path3 z 0)) hε)
    simpa only [Metric.mem_ball,dist_eq_norm,path3_at_zero] using h
  refine ⟨η,R,hη,hR,by linarith,?_⟩
  filter_upwards [path3_posDef_eventually z hz,he] with b hp hb
  have hs := hw (form3 (path3 z b)) hp hb
  refine ⟨hp,localWindow3_compact _ (by unfold lower3 min3; fun_prop) _ isCompact_Icc R,?_,hs.2⟩
  intro r hr n hn
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hs.1 r hr n hn)
  exact ⟨i,hi⟩

end D4.C23Local
