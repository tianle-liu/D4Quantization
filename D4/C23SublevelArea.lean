import D4.C23ClippedRectangle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The actual sublevel areas appearing in the local correction formulas. -/
noncomputable section
namespace D4.C23Local
open Set MeasureTheory AreaEnvelope

def translatedCoordinates (s : ℝ) : Plane ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).trans
    (MeasurableEquiv.addLeft (s,s))

theorem translatedCoordinates_apply (s : ℝ) (L : Plane) :
    translatedCoordinates s L = (L 0+s,L 1+s) := by
  simp [translatedCoordinates,add_comm]

theorem translatedCoordinates_preserving (s : ℝ) :
    MeasurePreserving (translatedCoordinates s) volume volume := by
  letI : (volume : Measure (ℝ × ℝ)).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]
    infer_instance
  exact (measurePreserving_add_left (volume : Measure (ℝ × ℝ)) (s,s)).comp
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))

theorem gap2_sublevel_area (p q r s : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    volume.real {L : Plane | gap2 p q r L ≤ s} =
      4*(p*q+p*r+q*r)+4*(p+q+r)*s+2*s^2 := by
  have he : {L : Plane | gap2 p q r L ≤ s} = (translatedCoordinates s) ⁻¹'
      clippedRectangle (2*(p+r+s)) (2*(q+r+s)) (2*r+s) s := by
    ext L
    simp only [mem_preimage,mem_setOf_eq,translatedCoordinates_apply]
    exact gap2_sublevel_translation p q r s hp hq hr hs L
  rw [he]
  have hm := (translatedCoordinates_preserving s).measure_preimage_equiv
    (clippedRectangle (2*(p+r+s)) (2*(q+r+s)) (2*r+s) s)
  rw [measureReal_def,hm,← measureReal_def,clippedRectangle_area _ _ _ _
    (by linarith) hs (by linarith) (by linarith)]
  ring

theorem gap3_sublevel_area (A B s : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : 0 ≤ s) :
    volume.real {L : Plane | gap3 A B L ≤ s} = A*B+2*(A+B)*s+3*s^2 := by
  have he : {L : Plane | gap3 A B L ≤ s} = (translatedCoordinates s) ⁻¹'
      clippedRectangle (A+2*s) (B+2*s) 0 s := by
    ext L
    simp only [mem_preimage,mem_setOf_eq,translatedCoordinates_apply]
    exact gap3_sublevel_translation A B s hA hB hs L
  rw [he]
  have hm := (translatedCoordinates_preserving s).measure_preimage_equiv
    (clippedRectangle (A+2*s) (B+2*s) 0 s)
  rw [measureReal_def,hm,← measureReal_def,clippedRectangle_area _ _ _ _
    (by norm_num) hs (by linarith) (by linarith)]
  ring

/-- Boundedness of the actual compact sublevel region, including degenerate
parameters. This supplies the compact domains required by layer cake. -/
theorem gap2_sublevel_compact (p q r s : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hs : 0 ≤ s) : IsCompact {L : Plane | gap2 p q r L ≤ s} := by
  have hc : IsClosed {L : Plane | gap2 p q r L ≤ s} :=
    isClosed_le (gap2_continuous p q r) continuous_const
  have hb : {L : Plane | gap2 p q r L ≤ s} ⊆
      Icc ![-s,-s] ![2*(p+r)+s,2*(q+r)+s] := by
    intro L hL
    obtain ⟨h1,h2,h3,h4,_⟩ := (gap2_le_iff p q r s hp hq hr hs L).mp hL
    constructor <;> intro i <;> fin_cases i <;> simp_all
  exact isCompact_Icc.of_isClosed_subset hc hb

theorem gap3_sublevel_compact (A B s : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : 0 ≤ s) : IsCompact {L : Plane | gap3 A B L ≤ s} := by
  have hc : IsClosed {L : Plane | gap3 A B L ≤ s} :=
    isClosed_le (gap3_continuous A B) continuous_const
  have hb : {L : Plane | gap3 A B L ≤ s} ⊆ Icc ![-s,-s] ![A+s,B+s] := by
    intro L hL
    obtain ⟨h1,h2,h3,h4,_⟩ := (gap3_le_iff A B s hA hB hs L).mp hL
    constructor <;> intro i <;> fin_cases i <;> simp_all
  exact isCompact_Icc.of_isClosed_subset hc hb

end D4.C23Local
