import D4.C23WindowMeasure
import D4.DualFiniteMinimum
import D4.AreaIntegral

/-! The four-dimensional local lower-envelope integral is the actual area integral. -/
noncomputable section
namespace D4.C23Local
open Matrix MeasureTheory Set Analytic AreaEnvelope

def windowEnvelope (U d : Plane → ℝ) (t : ℝ) (p : WindowCoordinates) : ℝ :=
  U p.1+min4 0 p.2.1 p.2.2 (p.2.1+p.2.2+t-d p.1)

theorem windowEnvelope_continuous {U d : Plane → ℝ} (hU : Continuous U)
    (hd : Continuous d) (t : ℝ) : Continuous (windowEnvelope U d t) := by
  unfold windowEnvelope min4
  fun_prop

theorem windowEnvelope_integral (K : Set Plane) (hK : IsCompact K) (R : ℝ)
    (U d : Plane → ℝ) (hU : Continuous U) (hd : Continuous d) (t : ℝ) :
    (15/4:ℝ)*(∫ p in referenceWindow K R,windowEnvelope U d t p)=
      areaIntegral K R U d t := by
  have hi : IntegrableOn (windowEnvelope U d t) (referenceWindow K R) :=
    (windowEnvelope_continuous hU hd t).continuousOn.integrableOn_compact
    (hK.prod (isCompact_Icc.prod isCompact_Icc))
  change (15/4:ℝ)*(∫ p in K ×ˢ (Icc (-R) R ×ˢ Icc (-R) R),
    windowEnvelope U d t p ∂((volume : Measure Plane).prod volume))=_
  rw [setIntegral_prod _ hi]
  simp only [areaIntegral,windowEnvelope,min4,min_assoc]

theorem windowSites2_minimum (z : Parameters) (p : WindowCoordinates) :
    Finset.univ.inf' Finset.univ_nonempty (fun i =>
      siteCost (form2 z) (windowPoint2 (form2 z) (lower2 (z 9)) p) (sites2 i)) =
      windowEnvelope (lower2 (z 9)) (gap2 (z 3) (z 4) (z 9)) (2*z 0) p := by
  rw [siteMinimum2]
  simp only [windowPoint2,coordinates2_inverse,fiberCoordinates,Matrix.cons_val,
    add_sub_cancel_right]
  have hp : ![p.1 0,p.1 1]=p.1 := by ext i; fin_cases i <;> rfl
  rw [hp]
  simp only [add_sub_cancel_right,windowEnvelope]

theorem windowSites3_minimum (z : Parameters) (p : WindowCoordinates) :
    let Q := form3 z
    let t := 2*Q 2 3
    let u := Q 0 0+Q 0 2+Q 0 3+t/2
    let v := Q 1 1+Q 1 2+Q 1 3+t/2
    Finset.univ.inf' Finset.univ_nonempty (fun i =>
      siteCost Q (windowPoint3 Q lower3 p) (sites3 i)) =
      windowEnvelope lower3 (gap3 (2*u-t) (2*v-t)) t p := by
  dsimp only
  rw [siteMinimum3]
  simp only [windowPoint3,coordinates3_inverse,fiberCoordinates,Matrix.cons_val,
    add_sub_cancel_right]
  have hp : ![p.1 0,p.1 1]=p.1 := by ext i; fin_cases i <;> rfl
  rw [hp]
  simp only [add_sub_cancel_right,windowEnvelope]

theorem localWindow2_dualIntegral (z : Parameters) (hQ : (form2 z).PosDef)
    (K : Set Plane) (hK : IsCompact K) (R : ℝ)
    (hcomplete : ∀ r∈localWindow2 (form2 z) (lower2 (z 9)) K R,∀ n : IntVec,
      quadratic (form2 z) (dualInverse (form2 z) r-castVec n)=dualNearest (form2 z) r →
        n∈Set.range sites2) :
    (15/4:ℝ)*(∫ r in localWindow2 (form2 z) (lower2 (z 9)) K R,
      dualNearest (form2 z) r) =
      (15/4:ℝ)*(∫ r in localWindow2 (form2 z) (lower2 (z 9)) K R,
        quadratic (form2 z)⁻¹ r/4)+
      areaIntegral K R (lower2 (z 9)) (gap2 (z 3) (z 4) (z 9)) (2*z 0) := by
  have hU : Continuous (lower2 (z 9)) := by unfold lower2 min4; fun_prop
  have hS : IsCompact (referenceWindow K R) := hK.prod (isCompact_Icc.prod isCompact_Icc)
  have he (p : WindowCoordinates) (hp : p∈referenceWindow K R) :
      dualNearest (form2 z) (windowPoint2 (form2 z) (lower2 (z 9)) p)=
        quadratic (form2 z)⁻¹ (windowPoint2 (form2 z) (lower2 (z 9)) p)/4+
          windowEnvelope (lower2 (z 9)) (gap2 (z 3) (z 4) (z 9)) (2*z 0) p := by
    rw [dualNearest_eq_finite_minimum hQ _ sites2
      (hcomplete _ ⟨p,hp,rfl⟩)]
    change _+Finset.univ.inf' _ (fun i => siteCost _ _ (sites2 i))=_
    rw [windowSites2_minimum]
  rw [localWindow2_integral _ _ hU,localWindow2_integral _ _ hU]
  rw [setIntegral_congr_fun hS.measurableSet he]
  have hiq : IntegrableOn (fun p => quadratic (form2 z)⁻¹
      (windowPoint2 (form2 z) (lower2 (z 9)) p)/4) (referenceWindow K R) :=
    (((quadratic_continuous _).comp (windowPoint2_continuous _ hU)).div_const 4).continuousOn.integrableOn_compact hS
  have hie : IntegrableOn (windowEnvelope (lower2 (z 9))
      (gap2 (z 3) (z 4) (z 9)) (2*z 0)) (referenceWindow K R) :=
    (windowEnvelope_continuous hU (gap2_continuous _ _ _) (2*z 0)).continuousOn.integrableOn_compact hS
  rw [integral_add hiq hie,mul_add,windowEnvelope_integral K hK R _ _ hU (gap2_continuous _ _ _)]

theorem localWindow3_dualIntegral (z : Parameters) (hQ : (form3 z).PosDef)
    (K : Set Plane) (hK : IsCompact K) (R : ℝ)
    (hcomplete : ∀ r∈localWindow3 (form3 z) lower3 K R,∀ n : IntVec,
      quadratic (form3 z) (dualInverse (form3 z) r-castVec n)=dualNearest (form3 z) r →
        n∈Set.range sites3) :
    let Q := form3 z
    let t := 2*Q 2 3
    let u := Q 0 0+Q 0 2+Q 0 3+t/2
    let v := Q 1 1+Q 1 2+Q 1 3+t/2
    (15/4:ℝ)*(∫ r in localWindow3 Q lower3 K R,dualNearest Q r) =
      (15/4:ℝ)*(∫ r in localWindow3 Q lower3 K R,quadratic Q⁻¹ r/4)+
        areaIntegral K R lower3 (gap3 (2*u-t) (2*v-t)) t := by
  dsimp only
  have hU : Continuous lower3 := by unfold lower3 min3; fun_prop
  have hS : IsCompact (referenceWindow K R) := hK.prod (isCompact_Icc.prod isCompact_Icc)
  have he (p : WindowCoordinates) (hp : p∈referenceWindow K R) :
      dualNearest (form3 z) (windowPoint3 (form3 z) lower3 p)=
        quadratic (form3 z)⁻¹ (windowPoint3 (form3 z) lower3 p)/4+
          windowEnvelope lower3
            (gap3 (2*(form3 z 0 0+form3 z 0 2+form3 z 0 3+2*form3 z 2 3/2)-2*form3 z 2 3)
              (2*(form3 z 1 1+form3 z 1 2+form3 z 1 3+2*form3 z 2 3/2)-2*form3 z 2 3))
            (2*form3 z 2 3) p := by
    rw [dualNearest_eq_finite_minimum hQ _ sites3
      (hcomplete _ ⟨p,hp,rfl⟩)]
    change _+Finset.univ.inf' _ (fun i => siteCost _ _ (sites3 i))=_
    rw [windowSites3_minimum]
  rw [localWindow3_integral _ _ hU,localWindow3_integral _ _ hU]
  rw [setIntegral_congr_fun hS.measurableSet he]
  have hiq : IntegrableOn (fun p => quadratic (form3 z)⁻¹
      (windowPoint3 (form3 z) lower3 p)/4) (referenceWindow K R) :=
    (((quadratic_continuous _).comp (windowPoint3_continuous _ hU)).div_const 4).continuousOn.integrableOn_compact hS
  have hie : IntegrableOn (windowEnvelope lower3
      (gap3 (2*(form3 z 0 0+form3 z 0 2+form3 z 0 3+2*form3 z 2 3/2)-2*form3 z 2 3)
        (2*(form3 z 1 1+form3 z 1 2+form3 z 1 3+2*form3 z 2 3/2)-2*form3 z 2 3))
      (2*form3 z 2 3)) (referenceWindow K R) :=
    (windowEnvelope_continuous hU (gap3_continuous
    (2*(form3 z 0 0+form3 z 0 2+form3 z 0 3+2*form3 z 2 3/2)-2*form3 z 2 3)
    (2*(form3 z 1 1+form3 z 1 2+form3 z 1 3+2*form3 z 2 3/2)-2*form3 z 2 3))
    (2*form3 z 2 3)).continuousOn.integrableOn_compact hS
  rw [integral_add hiq hie,mul_add,windowEnvelope_integral K hK R _ _ hU (gap3_continuous _ _)]

end D4.C23Local
