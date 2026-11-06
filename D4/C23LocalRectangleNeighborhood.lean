import D4.C23LocalRectangleCorrection
import D4.LocalWindowNeighborhood

noncomputable section
namespace D4.C23Local
open Set MeasureTheory AreaEnvelope

theorem localRectangle3_small_neighborhood (α β : ℝ) (hα : 0≤α) (hβ : 0≤β)
    (U : Set Plane) (hU : IsOpen U) (hz : {L | gap3 α β L=0}⊆U) :
    ∃ η : ℝ,0<η ∧ localRectangle3 α β η η⊆U := by
  obtain ⟨δ,hδ,_,hsub⟩ := gap3_small_sublevel α β hα hβ U hU hz
  refine ⟨δ/2,by positivity,?_⟩
  intro x hx
  apply hsub
  have hh := gap3_on_localRectangle α β (δ/2) 0 (by positivity) (by linarith) x hx
  simp only [sub_zero,add_zero] at hh
  change gap3 α β x≤δ
  linarith

theorem correction3_rectangle_nonpos (α β η R t : ℝ) (hη : 0≤η)
    (ht : -η≤t) (ht0 : t≤0) (hR : 2*η≤R) :
    areaIntegral (localRectangle3 α β η η) R lower3 (gap3 (α-t) (β-t)) t=
      negativeAreaIntegral (localRectangle3 α β η η) R lower3 (gap3 (α-t) (β-t)) t := by
  have hU : Continuous lower3 := by unfold lower3 min3; fun_prop
  apply areaIntegral_eq_negative_of_nonpos _
    (show IsCompact (localRectangle3 α β η η) from isCompact_Icc) R (by linarith)
    lower3 (gap3 (α-t) (β-t)) hU.continuousOn (gap3_continuous _ _).continuousOn
    (fun x _ => gap3_nonneg _ _ x) t ht0
  intro x hx
  have hg := gap3_on_localRectangle α β η t hη ht x hx
  have hn := gap3_nonneg (α-t) (β-t) x
  apply abs_le.mpr
  constructor <;> linarith

end D4.C23Local
