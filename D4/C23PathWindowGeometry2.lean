import D4.C23WindowLocalization2
import D4.C23PathLocalIntegrals

/-! The actual embedded windows have complete nearest-site lists along both paths. -/
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic AreaEnvelope
attribute [local instance] Matrix.normedAddCommGroup

def ValidLocalWindow (Q : Gram) (W : Set Vec) {ι : Type*} (sites : ι → IntVec) : Prop :=
  Q.PosDef ∧ IsCompact W ∧
    (∀ r∈W,∀ n : IntVec,quadratic Q (dualInverse Q r-castVec n)=dualNearest Q r →
      n∈Set.range sites) ∧
    (∀ r∈W,∀ n : IntVec,r+dualMap Q (castVec n)∈W → n=0)

theorem path2_valid_windows (z : Parameters) (hz : ∀ i,0<z i) :
    ∃ η R : ℝ,0<η ∧ 0<R ∧ 2*η≤R ∧
      ∀ᶠ a in nhds (0:ℝ),ValidLocalWindow (form2 (path2 z a)) (path2Window z η R a) sites2 := by
  obtain ⟨η,R,ε,hη,hR,hηR,hε,hw⟩ :=
    boundary2_localWindow_sites z (fun i => (hz i).le) (fun i _ => hz i)
  have hc : ContinuousAt (fun a => form2 (path2 z a)) 0 :=
    continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
      (form2_analyticAt (path2 z) 0 (path2_analytic z 0) i j).continuousAt
  have he : ∀ᶠ a in nhds (0:ℝ),‖form2 (path2 z a)-boundary2Form z‖<ε := by
    have h := hc.eventually (Metric.ball_mem_nhds (form2 (path2 z 0)) hε)
    simpa only [Metric.mem_ball,dist_eq_norm,path2_at_zero] using h
  refine ⟨η,R,hη,hR,by linarith,?_⟩
  filter_upwards [path2_posDef_eventually z hz,he] with a hp ha
  have hs := hw (form2 (path2 z a)) hp ha
  refine ⟨hp,localWindow2_compact _ (by unfold lower2 min4; fun_prop) _
    (gap2_sublevel_compact _ _ _ η (hz 3).le (hz 4).le (hz 9).le hη.le) R,?_,hs.2⟩
  intro r hr n hn
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hs.1 r hr n hn)
  exact ⟨i,hi⟩

end D4.C23Local
