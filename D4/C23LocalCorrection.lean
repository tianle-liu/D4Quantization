import D4.C23SublevelArea
import D4.C23CorrectionIntegral

/-! The square-envelope correction on the actual compact local sublevel
regions, with every sublevel area and final integral evaluated. -/
noncomputable section
namespace D4.C23Local
open Set MeasureTheory AreaEnvelope

private theorem sublevel_within (d : Plane → ℝ) (η s : ℝ) (hs : s ≤ η) :
    {L : Plane | L ∈ {L | d L ≤ η} ∧ d L ≤ s} = {L | d L ≤ s} := by
  ext L
  exact ⟨fun h => h.2,fun h => ⟨le_trans h hs,h⟩⟩

theorem correction2_actual (p q r a η R : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (ha : 0 ≤ a) (haη : 2*a ≤ η) (hR : η ≤ R) :
    let K := {L : Plane | gap2 p q r L ≤ η}
    areaIntegral K R (lower2 r) (gap2 p q r) (2*a) -
      negativeAreaIntegral K R (lower2 r) (gap2 p q r) (2*a) =
      2*a^3*(2*a^2+5*a*(p+q+r)+10*(p*q+p*r+q*r)) := by
  dsimp only
  have hη : 0 ≤ η := by linarith
  have hK := gap2_sublevel_compact p q r η hp hq hr hη
  have hU : Continuous (lower2 r) := by unfold lower2 min4; fun_prop
  rw [areaIntegral_sublevel _ hK R (by linarith) (lower2 r) (gap2 p q r)
    hU.continuousOn (gap2_continuous p q r).continuousOn
    (fun L _ => gap2_nonneg p q r L) (2*a) (by linarith) (by
      intro L hL
      simp only [mem_setOf_eq] at hL
      apply abs_le.mpr
      have hn := gap2_nonneg p q r L
      constructor <;> linarith [hL])]
  calc
    _ = (15/8:ℝ)*(∫ s in Icc 0 (2*a), (2*a-s)^2*
        (4*(p*q+p*r+q*r)+4*(p+q+r)*s+2*s^2)) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      rw [sublevel_within _ η s (by linarith [hs.2]),
        gap2_sublevel_area p q r s hp hq hr hs.1]
    _ = _ := correction2_integral a p q r ha

theorem correction3_actual (u v b η R : ℝ) (hb : 0 ≤ b)
    (hu : b ≤ u) (hv : b ≤ v) (hbη : 2*b ≤ η) (hR : η ≤ R) :
    let A := 2*u-2*b
    let B := 2*v-2*b
    let K := {L : Plane | gap3 A B L ≤ η}
    areaIntegral K R lower3 (gap3 A B) (2*b) -
      negativeAreaIntegral K R lower3 (gap3 A B) (2*b) =
      2*b^3*(3*b^2-5*b*(u+v)+10*u*v) := by
  dsimp only
  have hη : 0 ≤ η := by linarith
  have hA : 0 ≤ 2*u-2*b := by linarith
  have hB : 0 ≤ 2*v-2*b := by linarith
  have hK := gap3_sublevel_compact (2*u-2*b) (2*v-2*b) η hA hB hη
  have hU : Continuous lower3 := by unfold lower3 min3; fun_prop
  rw [areaIntegral_sublevel _ hK R (by linarith) lower3 (gap3 (2*u-2*b) (2*v-2*b))
    hU.continuousOn (gap3_continuous _ _).continuousOn
    (fun L _ => gap3_nonneg _ _ L) (2*b) (by linarith) (by
      intro L hL
      simp only [mem_setOf_eq] at hL
      apply abs_le.mpr
      have hn := gap3_nonneg (2*u-2*b) (2*v-2*b) L
      constructor <;> linarith [hL])]
  calc
    _ = (15/8:ℝ)*(∫ s in Icc 0 (2*b), (2*b-s)^2*
        ((2*u-2*b)*(2*v-2*b)+2*((2*u-2*b)+(2*v-2*b))*s+3*s^2)) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      rw [sublevel_within _ η s (by linarith [hs.2]),
        gap3_sublevel_area _ _ s hA hB hs.1]
    _ = _ := correction3_integral b u v hb


/-- The C₃ correction on one fixed neighborhood of the common face. The
integration domain is defined at `b = 0`, not changed with the deformation. -/
theorem correction3_actual_fixed_domain (u v b η R : ℝ) (hb : 0 ≤ b)
    (hu : b ≤ u) (hv : b ≤ v) (hbη : 2*b ≤ η) (hR : η ≤ R) :
    let K := {L : Plane | gap3 (2*u) (2*v) L ≤ η}
    areaIntegral K R lower3 (gap3 (2*u-2*b) (2*v-2*b)) (2*b) -
      negativeAreaIntegral K R lower3 (gap3 (2*u-2*b) (2*v-2*b)) (2*b) =
      2*b^3*(3*b^2-5*b*(u+v)+10*u*v) := by
  dsimp only
  have hη : 0 ≤ η := by linarith
  have hA : 0 ≤ 2*u-2*b := by linarith
  have hB : 0 ≤ 2*v-2*b := by linarith
  have hK := gap3_sublevel_compact (2*u) (2*v) η (by linarith) (by linarith) hη
  have hU : Continuous lower3 := by unfold lower3 min3; fun_prop
  rw [areaIntegral_sublevel _ hK R (by linarith) lower3 (gap3 (2*u-2*b) (2*v-2*b))
    hU.continuousOn (gap3_continuous _ _).continuousOn
    (fun L _ => gap3_nonneg _ _ L) (2*b) (by linarith) (by
      intro L hL
      simp only [mem_setOf_eq] at hL
      apply abs_le.mpr
      have hn := gap3_nonneg (2*u-2*b) (2*v-2*b) L
      have hh := gap3_shift_bounds (2*u) (2*v) (2*b) (by linarith) L
      constructor <;> linarith [hL,hh.2])]
  calc
    _ = (15/8:ℝ)*(∫ s in Icc 0 (2*b), (2*b-s)^2*
        ((2*u-2*b)*(2*v-2*b)+2*((2*u-2*b)+(2*v-2*b))*s+3*s^2)) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      have he : {L : Plane | L ∈ {L | gap3 (2*u) (2*v) L ≤ η} ∧
          gap3 (2*u-2*b) (2*v-2*b) L ≤ s} =
          {L | gap3 (2*u-2*b) (2*v-2*b) L ≤ s} := by
        ext L
        constructor
        · exact fun h => h.2
        · intro h
          simp only [mem_setOf_eq] at h ⊢
          have hh := gap3_shift_bounds (2*u) (2*v) (2*b) (by linarith) L
          exact ⟨by linarith [hh.1,hs.2],h⟩
      rw [he,gap3_sublevel_area _ _ s hA hB hs.1]
    _ = _ := correction3_integral b u v hb

end D4.C23Local
