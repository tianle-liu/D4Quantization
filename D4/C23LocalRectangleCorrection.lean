import D4.C23LocalPartitionC3
import D4.C23LocalCorrection

/-! The C₂/C₃ correction on the fixed rectangular window used for its
explicit seven-region analytic subdivision. -/
noncomputable section
namespace D4.C23Local
open Set MeasureTheory AreaEnvelope

theorem gap3_on_localRectangle (α β η t : ℝ) (hη : 0≤η) (ht : -η≤t)
    (x : Plane) (hx : x∈localRectangle3 α β η η) :
    gap3 (α-t) (β-t) x≤2*η+t := by
  have hl0 : -η≤x 0 := hx.1 0
  have hl1 : -η≤x 1 := hx.1 1
  have hu0 : x 0≤α+η := hx.2 0
  have hu1 : x 1≤β+η := hx.2 1
  have hU : -η≤lower3 x := by
    unfold lower3 min3
    exact le_min (by linarith) (le_min hl0 hl1)
  have hV : -η-t≤upper3 (α-t) (β-t) x := by
    unfold upper3 min3
    exact le_min (by linarith) (le_min (by linarith) (by linarith))
  unfold gap3
  linarith

theorem gap3_sublevel_in_localRectangle (α β η t s : ℝ)
    (hA : 0≤α-t) (hB : 0≤β-t) (hs : 0≤s) (hst : s≤t) (htη : t≤η) :
    {x : Plane | gap3 (α-t) (β-t) x≤s}⊆localRectangle3 α β η η := by
  intro x hx
  obtain ⟨h1,h2,h3,h4,_⟩ := (gap3_le_iff (α-t) (β-t) s hA hB hs x).mp hx
  constructor <;> intro j <;> fin_cases j <;> dsimp <;> linarith

theorem correction3_actual_rectangle (u v b η R : ℝ) (hb : 0≤b)
    (hu : b≤u) (hv : b≤v) (hbη : 2*b≤η) (hR : 2*η≤R) :
    areaIntegral (localRectangle3 (2*u) (2*v) η η) R lower3
      (gap3 (2*u-2*b) (2*v-2*b)) (2*b) -
    negativeAreaIntegral (localRectangle3 (2*u) (2*v) η η) R lower3
      (gap3 (2*u-2*b) (2*v-2*b)) (2*b) =
      2*b^3*(3*b^2-5*b*(u+v)+10*u*v) := by
  have hη : 0≤η := by linarith
  have hA : 0≤2*u-2*b := by linarith
  have hB : 0≤2*v-2*b := by linarith
  have hU : Continuous lower3 := by unfold lower3 min3; fun_prop
  rw [areaIntegral_sublevel (localRectangle3 (2*u) (2*v) η η)
    (show IsCompact (localRectangle3 (2*u) (2*v) η η) from isCompact_Icc) R (by linarith) lower3
    (gap3 (2*u-2*b) (2*v-2*b)) hU.continuousOn (gap3_continuous _ _).continuousOn
    (fun x _ => gap3_nonneg _ _ x) (2*b) (by linarith) (by
      intro x hx
      apply abs_le.mpr
      have hg := gap3_on_localRectangle (2*u) (2*v) η (2*b) hη (by linarith) x hx
      have hn := gap3_nonneg (2*u-2*b) (2*v-2*b) x
      constructor <;> linarith)]
  calc
    _ = (15/8:ℝ)*(∫ s in Icc 0 (2*b), (2*b-s)^2*
        ((2*u-2*b)*(2*v-2*b)+2*((2*u-2*b)+(2*v-2*b))*s+3*s^2)) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      have he : {x : Plane | x∈localRectangle3 (2*u) (2*v) η η ∧
          gap3 (2*u-2*b) (2*v-2*b) x≤s} =
          {x | gap3 (2*u-2*b) (2*v-2*b) x≤s} := by
        ext x
        constructor
        · exact fun h => h.2
        · intro hx
          exact ⟨gap3_sublevel_in_localRectangle (2*u) (2*v) η (2*b) s hA hB hs.1 hs.2 hbη hx,hx⟩
      rw [he,gap3_sublevel_area _ _ s hA hB hs.1]
    _ = _ := correction3_integral b u v hb

end D4.C23Local
