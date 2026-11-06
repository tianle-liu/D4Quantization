import D4.C23SublevelArea
import Mathlib.Topology.Order.Compact

/-! Small actual sublevel neighborhoods fit inside any prescribed open
neighborhood of their zero set. Compact parametrized images fit uniformly. -/
noncomputable section
namespace D4.Analytic
open Set Filter Topology

theorem positive_sublevel_subset {E : Type*} [TopologicalSpace E]
    (f : E → ℝ) (hf : Continuous f) (hn : ∀ x,0≤f x)
    (hc : IsCompact {x | f x≤1}) (U : Set E) (hU : IsOpen U)
    (hz : {x | f x=0}⊆U) : ∃ η : ℝ,0<η ∧ η≤1 ∧ {x | f x≤η}⊆U := by
  let K : Set E := {x | f x≤1}∩Uᶜ
  have hK : IsCompact K := hc.inter_right hU.isClosed_compl
  by_cases he : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn he hf.continuousOn
    have hp : 0<f x := lt_of_le_of_ne (hn x) (by
      intro h
      exact hx.2 (hz h.symm))
    refine ⟨min 1 (f x/2),lt_min (by norm_num) (by positivity),min_le_left _ _,?_⟩
    intro y hy
    apply Classical.byContradiction
    intro hny
    change f y≤min 1 (f x/2) at hy
    have hyK : y∈K := ⟨show f y≤1 from hy.trans (min_le_left _ _),hny⟩
    have hxy : f x≤f y := hmin hyK
    have hh := min_le_right (1:ℝ) (f x/2)
    linarith
  · refine ⟨1,by norm_num,le_rfl,?_⟩
    intro x hx
    apply Classical.byContradiction
    intro hnot
    exact he ⟨x,hx,hnot⟩

theorem compact_image_eventually_subset {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X × Y → Z) (hf : Continuous f) (x₀ : X) (K : Set Y) (hK : IsCompact K)
    (U : Set Z) (hU : IsOpen U) (hzero : ∀ y∈K,f (x₀,y)∈U) :
    ∀ᶠ x in nhds x₀,(fun y => f (x,y)) '' K⊆U := by
  have hh : ∀ᶠ x in nhds x₀,∀ y∈K,f (x,y)∈U := by
    apply hK.eventually_forall_of_forall_eventually
    intro y hy
    exact hf.continuousAt (hU.mem_nhds (hzero y hy))
  filter_upwards [hh] with x hx
  rintro _ ⟨y,hy,rfl⟩
  exact hx y hy

end D4.Analytic
namespace D4.C23Local
open Set AreaEnvelope

theorem gap2_small_sublevel (p q r : ℝ) (hp : 0≤p) (hq : 0≤q) (hr : 0≤r)
    (U : Set Plane) (hU : IsOpen U) (hz : {L | gap2 p q r L=0}⊆U) :
    ∃ η : ℝ,0<η ∧ η≤1 ∧ {L | gap2 p q r L≤η}⊆U :=
  Analytic.positive_sublevel_subset _ (gap2_continuous p q r) (gap2_nonneg p q r)
    (gap2_sublevel_compact p q r 1 hp hq hr (by norm_num)) U hU hz

theorem gap3_small_sublevel (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (U : Set Plane) (hU : IsOpen U) (hz : {L | gap3 A B L=0}⊆U) :
    ∃ η : ℝ,0<η ∧ η≤1 ∧ {L | gap3 A B L≤η}⊆U :=
  Analytic.positive_sublevel_subset _ (gap3_continuous A B) (gap3_nonneg A B)
    (gap3_sublevel_compact A B 1 hA hB (by norm_num)) U hU hz

end D4.C23Local
