import D4.C23LocalWindow
import D4.LocalWindowNeighborhood
import D4.C23AnalyticPaths
import D4.PeriodicLocalization

/-! The actual local windows meet only uniformly finitely many translates
of the moving period parallelepiped, on both sides of each boundary path. -/
noncomputable section
namespace D4.C23Local
open Set Filter Topology Analytic AreaEnvelope
attribute [local instance] Matrix.normedAddCommGroup

private theorem periodWindow2_joint_continuous {U : Plane → ℝ} (hU : Continuous U) :
    Continuous (fun p : Gram×WindowCoordinates => windowPoint2 p.1 U p.2) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : Gram×WindowCoordinates => p.1 0 0-(p.2.2.1+U p.2.1)); fun_prop
  · change Continuous (fun p : Gram×WindowCoordinates => p.1 1 1-(p.2.2.2+U p.2.1)); fun_prop
  · change Continuous (fun p : Gram×WindowCoordinates => p.2.1 0-p.1 2 2); fun_prop
  · change Continuous (fun p : Gram×WindowCoordinates => p.2.1 1-p.1 3 3); fun_prop

private theorem periodWindow3_joint_continuous {U : Plane → ℝ} (hU : Continuous U) :
    Continuous (fun p : Gram×WindowCoordinates => windowPoint3 p.1 U p.2) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : Gram×WindowCoordinates => p.2.1 0-p.1 0 0); fun_prop
  · change Continuous (fun p : Gram×WindowCoordinates => p.2.1 1-p.1 1 1); fun_prop
  · change Continuous (fun p : Gram×WindowCoordinates => p.1 2 2-(p.2.2.1+U p.2.1)); fun_prop
  · change Continuous (fun p : Gram×WindowCoordinates => p.1 3 3-(p.2.2.2+U p.2.1)); fun_prop

theorem compact_window_finite_period_translates
    (P : Gram → WindowCoordinates → Vec)
    (hP : Continuous (fun p : Gram×WindowCoordinates => P p.1 p.2))
    (K : Set WindowCoordinates) (hK : IsCompact K) {Q : Gram} (hQ : Q.PosDef)
    (c : Vec) :
    ∃ s : Finset IntVec,∀ᶠ R : Gram in nhds Q,∀ n : IntVec,
      (dualPeriod R c ∩ dualTranslate R n (P R '' K)).Nonempty → n∈s := by
  have hc : IsCompact (P Q '' K) :=
    hK.image (hP.comp (continuous_const.prodMk continuous_id))
  obtain ⟨B,_,hB⟩ := hc.isBounded.exists_pos_norm_lt
  have hw : ∀ᶠ R : Gram in nhds Q,P R '' K⊆Metric.ball 0 B :=
    compact_image_eventually_subset _ hP Q K hK (Metric.ball 0 B) Metric.isOpen_ball (by
      intro p hp
      simpa only [Metric.mem_ball,dist_zero_right] using hB (P Q p) ⟨p,hp,rfl⟩)
  obtain ⟨ε,hε,s,hs⟩ := uniform_finite_dualPeriod_translates hQ c B
  have he : ∀ᶠ R : Gram in nhds Q,‖R-Q‖<ε := by
    simpa only [Metric.mem_ball,dist_eq_norm] using Metric.ball_mem_nhds Q hε
  refine ⟨s,?_⟩
  filter_upwards [hw,he] with R hwin hR
  apply hs R hR (P R '' K)
  intro w hw
  exact (show ‖w‖<B by simpa only [Metric.mem_ball,dist_zero_right] using hwin hw).le

theorem localWindow2_finite_period_translates {Q : Gram} (hQ : Q.PosDef)
    (U : Plane → ℝ) (hU : Continuous U) (K : Set Plane) (hK : IsCompact K)
    (R : ℝ) (c : Vec) :
    ∃ s : Finset IntVec,∀ᶠ A : Gram in nhds Q,∀ n : IntVec,
      (dualPeriod A c ∩ dualTranslate A n (localWindow2 A U K R)).Nonempty → n∈s :=
  compact_window_finite_period_translates (fun A => windowPoint2 A U)
    (periodWindow2_joint_continuous hU) (referenceWindow K R)
    (hK.prod (isCompact_Icc.prod isCompact_Icc)) hQ c

theorem localWindow3_finite_period_translates {Q : Gram} (hQ : Q.PosDef)
    (U : Plane → ℝ) (hU : Continuous U) (K : Set Plane) (hK : IsCompact K)
    (R : ℝ) (c : Vec) :
    ∃ s : Finset IntVec,∀ᶠ A : Gram in nhds Q,∀ n : IntVec,
      (dualPeriod A c ∩ dualTranslate A n (localWindow3 A U K R)).Nonempty → n∈s :=
  compact_window_finite_period_translates (fun A => windowPoint3 A U)
    (periodWindow3_joint_continuous hU) (referenceWindow K R)
    (hK.prod (isCompact_Icc.prod isCompact_Icc)) hQ c

theorem path2_finite_window_translates (z : Parameters) (hz : ∀ i,0<z i)
    (K : Set Plane) (hK : IsCompact K) (R : ℝ) (c : Vec) :
    ∃ s : Finset IntVec,∀ᶠ a : ℝ in nhds 0,∀ n : IntVec,
      (dualPeriod (form2 (path2 z a)) c ∩
        dualTranslate (form2 (path2 z a)) n
          (localWindow2 (form2 (path2 z a)) (lower2 (z 9)) K R)).Nonempty → n∈s := by
  have hQ : (form2 (path2 z 0)).PosDef := by
    rw [path2_at_zero]
    exact boundary2_posDef z (fun i => (hz i).le) (fun i _ => hz i)
  obtain ⟨s,hs⟩ := localWindow2_finite_period_translates hQ (lower2 (z 9))
    (by unfold lower2 min4; fun_prop) K hK R c
  refine ⟨s,?_⟩
  have hcont : ContinuousAt (fun a => form2 (path2 z a)) 0 :=
    continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
      (form2_analyticAt (path2 z) 0 (path2_analytic z 0) i j).continuousAt
  exact hcont hs

theorem path3_finite_window_translates (z : Parameters) (hz : ∀ i,0<z i)
    (K : Set Plane) (hK : IsCompact K) (R : ℝ) (c : Vec) :
    ∃ s : Finset IntVec,∀ᶠ b : ℝ in nhds 0,∀ n : IntVec,
      (dualPeriod (form3 (path3 z b)) c ∩
        dualTranslate (form3 (path3 z b)) n
          (localWindow3 (form3 (path3 z b)) lower3 K R)).Nonempty → n∈s := by
  have hQ : (form3 (path3 z 0)).PosDef := by
    rw [path3_at_zero]
    exact boundary3_posDef z (fun i => (hz i).le) (fun i _ => hz i)
  obtain ⟨s,hs⟩ := localWindow3_finite_period_translates hQ lower3
    (by unfold lower3 min3; fun_prop) K hK R c
  refine ⟨s,?_⟩
  have hcont : ContinuousAt (fun b => form3 (path3 z b)) 0 :=
    continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
      (form3_analyticAt (path3 z) 0 (path3_analytic z 0) i j).continuousAt
  exact hcont hs

end D4.C23Local
