import D4.C23WindowEnvelope
import D4.C23WindowQuadratic
import D4.C23PathNeighborhoods
import D4.C23LocalPathCorrection

/-! The actual four-dimensional window integrals along the two boundary paths. -/
noncomputable section
namespace D4.C23Local
open Matrix Set MeasureTheory Analytic AreaEnvelope

def path2Window (z : Parameters) (η R a : ℝ) : Set Vec :=
  localWindow2 (form2 (path2 z a)) (lower2 (z 9))
    {L | gap2 (z 3) (z 4) (z 9) L≤η} R

def path3Window (z : Parameters) (η R b : ℝ) : Set Vec :=
  localWindow3 (form3 (path3 z b)) lower3
    (localRectangle3 (2*z 1) (2*z 2) η η) R

def path2WindowBaseline (z : Parameters) (η R a : ℝ) : ℝ :=
  (15/4:ℝ)*(∫ r in path2Window z η R a,quadratic (form2 (path2 z a))⁻¹ r/4)+
    path2LocalBaseline z η R a

def path3WindowBaseline (z : Parameters) (η R b : ℝ) : ℝ :=
  (15/4:ℝ)*(∫ r in path3Window z η R b,quadratic (form3 (path3 z b))⁻¹ r/4)+
    path3LocalBaseline z η R b

theorem path2WindowBaseline_analytic (z : Parameters) (hz : ∀ i,0<z i)
    (η R : ℝ) (hη : 0≤η) : AnalyticAt ℝ (path2WindowBaseline z η R) 0 := by
  have hQ : (form2 (path2 z 0)).PosDef := by
    rw [path2_at_zero]
    exact boundary2_posDef z (fun i => (hz i).le) (fun i _ => hz i)
  exact (analyticAt_const.mul (localWindow2_quadratic_analytic (fun a => form2 (path2 z a)) 0
    (form2_analyticAt (path2 z) 0 (path2_analytic z 0)) hQ.det_pos.ne'
    (lower2 (z 9)) (by unfold lower2 min4; fun_prop) _
    (gap2_sublevel_compact _ _ _ η (hz 3).le (hz 4).le (hz 9).le hη) R)).add
    (path2LocalBaseline_analytic z η R 0 (hz 3).le (hz 4).le (hz 9).le hη)

theorem path3WindowBaseline_analytic (z : Parameters) (hz : ∀ i,0<z i)
    (η R : ℝ) (hη : 0<η) : AnalyticAt ℝ (path3WindowBaseline z η R) 0 := by
  have hQ : (form3 (path3 z 0)).PosDef := by
    rw [path3_at_zero]
    exact boundary3_posDef z (fun i => (hz i).le) (fun i _ => hz i)
  exact (analyticAt_const.mul (localWindow3_quadratic_analytic (fun b => form3 (path3 z b)) 0
    (form3_analyticAt (path3 z) 0 (path3_analytic z 0)) hQ.det_pos.ne'
    lower3 (by unfold lower3 min3; fun_prop) _ isCompact_Icc R)).add
    (path3LocalBaseline_analytic z η R (hz 1) (hz 2) hη)

theorem path2_window_correction (z : Parameters) (hz : ∀ i,0<z i)
    (η R : ℝ) (hη : 0<η) (hR : 2*η≤R)
    (hcomplete : ∀ᶠ a in nhds (0:ℝ),∀ r∈path2Window z η R a,∀ n : IntVec,
      quadratic (form2 (path2 z a)) (dualInverse (form2 (path2 z a)) r-castVec n)=
        dualNearest (form2 (path2 z a)) r → n∈Set.range sites2) :
    ∀ᶠ a in nhds (0:ℝ),
      (15/4:ℝ)*(∫ r in path2Window z η R a,dualNearest (form2 (path2 z a)) r)=
        path2WindowBaseline z η R a+path2Correction z a := by
  filter_upwards [hcomplete,path2_posDef_eventually z hz,
    path2_local_correction z η R (hz 3).le (hz 4).le (hz 9).le hη hR]
    with a hc hp ha
  have he := localWindow2_dualIntegral (path2 z a) hp
    {L | gap2 (z 3) (z 4) (z 9) L≤η}
    (gap2_sublevel_compact _ _ _ η (hz 3).le (hz 4).le (hz 9).le hη.le) R hc
  change (15/4:ℝ)*(∫ r in path2Window z η R a,dualNearest (form2 (path2 z a)) r)=
    (15/4:ℝ)*(∫ r in path2Window z η R a,quadratic (form2 (path2 z a))⁻¹ r/4)+
      areaIntegral _ R (lower2 (z 9)) (gap2 (z 3) (z 4) (z 9)) (2*a) at he
  rw [he,ha]
  unfold path2WindowBaseline
  ring

theorem path3_window_correction (z : Parameters) (hz : ∀ i,0<z i)
    (η R : ℝ) (hη : 0<η) (hR : 2*η≤R)
    (hcomplete : ∀ᶠ b in nhds (0:ℝ),∀ r∈path3Window z η R b,∀ n : IntVec,
      quadratic (form3 (path3 z b)) (dualInverse (form3 (path3 z b)) r-castVec n)=
        dualNearest (form3 (path3 z b)) r → n∈Set.range sites3) :
    ∀ᶠ b in nhds (0:ℝ),
      (15/4:ℝ)*(∫ r in path3Window z η R b,dualNearest (form3 (path3 z b)) r)=
        path3WindowBaseline z η R b+path3Correction z b := by
  filter_upwards [hcomplete,path3_posDef_eventually z hz,
    path3_local_correction z η R (hz 1) (hz 2) hη hR] with b hc hp hb
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
  rw [he,hb]
  unfold path3WindowBaseline
  ring

end D4.C23Local
