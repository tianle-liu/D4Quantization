import D4.C23PathLocalIntegrals
import D4.C23JointPaths

noncomputable section
namespace D4.C23Local
open Set MeasureTheory Filter Topology AreaEnvelope Analytic

theorem path2_local_correction_joint (z : Parameters) (hz : ∀i,0<z i) (η R : ℝ)
    (hη : 0<η) (hR : 2*η≤R) :
    ∀ᶠ p : Parameters×ℝ in nhds (z,0),
      areaIntegral {L : Plane | gap2 (p.1 3) (p.1 4) (p.1 9) L≤η}
        R (lower2 (p.1 9)) (gap2 (p.1 3) (p.1 4) (p.1 9)) (2*p.2)=
      path2LocalBaseline p.1 η R p.2+path2Correction p.1 p.2 := by
  have htw : ContinuousAt (fun p : Parameters×ℝ => 2*p.2) (z,0) := by fun_prop
  filter_upwards [Joint.positive_eventually z hz,
    htw.eventually_const_lt (show -η<2*(0:ℝ) by linarith),
    htw.eventually_lt_const (show 2*(0:ℝ)<η by linarith)] with p hp hlo hhi
  rcases p with ⟨z,a⟩
  have h3:0≤z 3 := (hp 3).le
  have h4:0≤z 4 := (hp 4).le
  have h9:0≤z 9 := (hp 9).le
  by_cases ha : 0≤a
  · rw [path2Correction,if_pos ha]
    have h := correction2_actual (z 3) (z 4) (z 9) a η R h3 h4 h9 ha hhi.le (by linarith)
    change _-path2LocalBaseline z η R a=_ at h
    linarith
  · rw [path2Correction,if_neg ha,add_zero]
    change areaIntegral _ _ _ _ _=negativeAreaIntegral _ _ _ _ _
    have hU : Continuous (lower2 (z 9)) := by unfold lower2 min4; fun_prop
    apply areaIntegral_eq_negative_of_nonpos _
      (gap2_sublevel_compact (z 3) (z 4) (z 9) η h3 h4 h9 hη.le)
      R (by linarith) _ _ hU.continuousOn (gap2_continuous _ _ _).continuousOn
      (fun L _ => gap2_nonneg _ _ _ L) (2*a) (by linarith)
    intro L hL
    have hn := gap2_nonneg (z 3) (z 4) (z 9) L
    change gap2 (z 3) (z 4) (z 9) L≤η at hL
    apply abs_le.mpr
    constructor <;> linarith

theorem path3_local_correction_joint (z : Parameters) (hz : ∀i,0<z i) (η R : ℝ)
    (hη : 0<η) (hR : 2*η≤R) :
    ∀ᶠ p : Parameters×ℝ in nhds (z,0),
      areaIntegral (localRectangle3 (2*p.1 1) (2*p.1 2) η η)
        R lower3 (gap3 (2*p.1 1-2*p.2) (2*p.1 2-2*p.2)) (2*p.2)=
      path3LocalBaseline p.1 η R p.2+path3Correction p.1 p.2 := by
  have htw : ContinuousAt (fun p : Parameters×ℝ => 2*p.2) (z,0) := by fun_prop
  have he (i : Fin 10) : ∀ᶠ p : Parameters×ℝ in nhds (z,0),p.2<p.1 i := by
    exact ((Joint.coordinate_analytic (z,0) i).continuousAt.sub continuousAt_snd).eventually_const_lt
      (by simpa using hz i) |>.mono fun p hp=>by linarith
  filter_upwards [htw.eventually_const_lt (show -η<2*(0:ℝ) by linarith),
    htw.eventually_lt_const (show 2*(0:ℝ)<η by linarith),he 1,he 2] with p hlo hhi h1 h2
  rcases p with ⟨z,b⟩
  dsimp only at hlo hhi h1 h2 ⊢
  by_cases hb : 0≤b
  · rw [path3Correction,if_pos hb]
    have h := correction3_actual_rectangle (z 1) (z 2) b η R hb h1.le h2.le hhi.le hR
    change _-path3LocalBaseline z η R b=_ at h
    linarith
  · rw [path3Correction,if_neg hb,add_zero]
    exact correction3_rectangle_nonpos (2*z 1) (2*z 2) η R (2*b) hη.le hlo.le
      (by linarith) hR

theorem path2_window_correction_joint (z : Parameters) (hz : ∀ i,0<z i)
    (η R : ℝ) (hη : 0<η) (hR : 2*η≤R)
    (hcomplete : ∀ᶠ p : Parameters×ℝ in nhds (z,0),∀ r∈path2Window p.1 η R p.2,∀ n : IntVec,
      quadratic (form2 (path2 p.1 p.2)) (dualInverse (form2 (path2 p.1 p.2)) r-castVec n)=
        dualNearest (form2 (path2 p.1 p.2)) r → n∈Set.range sites2) :
    ∀ᶠ p : Parameters×ℝ in nhds (z,0),
      (15/4:ℝ)*(∫ r in path2Window p.1 η R p.2,dualNearest (form2 (path2 p.1 p.2)) r)=
        path2WindowBaseline p.1 η R p.2+path2Correction p.1 p.2 := by
  filter_upwards [hcomplete,Joint.positive_eventually z hz,Joint.path2_posDef_eventually z hz,
    path2_local_correction_joint z hz η R hη hR] with p hc hpos hp hcorr
  rcases p with ⟨z,a⟩
  dsimp only at hc hpos hp hcorr ⊢
  have he := localWindow2_dualIntegral (path2 z a) hp
    {L | gap2 (z 3) (z 4) (z 9) L≤η}
    (gap2_sublevel_compact _ _ _ η (hpos 3).le (hpos 4).le (hpos 9).le hη.le) R hc
  change (15/4:ℝ)*(∫ r in path2Window z η R a,dualNearest (form2 (path2 z a)) r)=
    (15/4:ℝ)*(∫ r in path2Window z η R a,quadratic (form2 (path2 z a))⁻¹ r/4)+
      areaIntegral _ R (lower2 (z 9)) (gap2 (z 3) (z 4) (z 9)) (2*a) at he
  rw [he,hcorr]
  unfold path2WindowBaseline
  ring

theorem path3_window_correction_joint (z : Parameters) (hz : ∀ i,0<z i)
    (η R : ℝ) (hη : 0<η) (hR : 2*η≤R)
    (hcomplete : ∀ᶠ p : Parameters×ℝ in nhds (z,0),∀ r∈path3Window p.1 η R p.2,∀ n : IntVec,
      quadratic (form3 (path3 p.1 p.2)) (dualInverse (form3 (path3 p.1 p.2)) r-castVec n)=
        dualNearest (form3 (path3 p.1 p.2)) r → n∈Set.range sites3) :
    ∀ᶠ p : Parameters×ℝ in nhds (z,0),
      (15/4:ℝ)*(∫ r in path3Window p.1 η R p.2,dualNearest (form3 (path3 p.1 p.2)) r)=
        path3WindowBaseline p.1 η R p.2+path3Correction p.1 p.2 := by
  filter_upwards [hcomplete,Joint.positive_eventually z hz,Joint.path3_posDef_eventually z hz,
    path3_local_correction_joint z hz η R hη hR] with p hc hpos hp hcorr
  rcases p with ⟨z,b⟩
  dsimp only at hc hpos hp hcorr ⊢
  have he := localWindow3_dualIntegral (path3 z b) hp
    (localRectangle3 (2*z 1) (2*z 2) η η) isCompact_Icc R hc
  dsimp only at he
  have hf := path3_fixed_parameters z b
  dsimp only at hf
  rw [show 2*form3 (path3 z b) 2 3/2=form3 (path3 z b) 2 3 by ring,
    hf.2.1,hf.2.2,hf.1] at he
  change (15/4:ℝ)*(∫ r in path3Window z η R b,dualNearest (form3 (path3 z b)) r)=
    (15/4:ℝ)*(∫ r in path3Window z η R b,quadratic (form3 (path3 z b))⁻¹ r/4)+
      areaIntegral _ R lower3 (gap3 (2*z 1-2*b) (2*z 2-2*b)) (2*b) at he
  rw [he,hcorr]
  unfold path3WindowBaseline
  ring


end D4.C23Local
