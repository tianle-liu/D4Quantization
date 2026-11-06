import D4.PrincipalGraphList
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace D4.PrincipalGraphs
open SimpleGraph

def edgeLo : Fin 10 → Fin 5 := ![0,0,0,0,1,1,1,2,2,3]
def edgeHi : Fin 10 → Fin 5 := ![1,2,3,4,2,3,4,3,4,4]

def graph (H : Finset (Fin 10)) : SimpleGraph (Fin 5) where
  Adj u v := u ≠ v ∧ ∃ e ∈ H,
    (u=edgeLo e ∧ v=edgeHi e) ∨ (u=edgeHi e ∧ v=edgeLo e)
  symm := by rintro u v ⟨hn,e,he,h|h⟩ <;> exact ⟨hn.symm,e,he,by tauto⟩
  loopless := by intro v h; exact h.1 rfl

instance graph_decidable (H : Finset (Fin 10)) : DecidableRel (graph H).Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ ∃ e ∈ H,
    (u=edgeLo e ∧ v=edgeHi e) ∨ (u=edgeHi e ∧ v=edgeLo e)))

def incident (v : Fin 5) (e : Fin 10) : Prop := v=edgeLo e ∨ v=edgeHi e
instance (v : Fin 5) (e : Fin 10) : Decidable (incident v e) :=
  inferInstanceAs (Decidable (v=edgeLo e ∨ v=edgeHi e))
def other (v : Fin 5) (e : Fin 10) : Fin 5 := if v=edgeLo e then edgeHi e else edgeLo e
def degreeFast (H : Finset (Fin 10)) (v : Fin 5) := (H.filter (incident v)).card

theorem endpoints_distinct : ∀ e : Fin 10, edgeLo e ≠ edgeHi e := by decide +kernel

theorem edge_adj {H : Finset (Fin 10)} {e : Fin 10} (he : e ∈ H) :
    (graph H).Adj (edgeLo e) (edgeHi e) := ⟨endpoints_distinct e,e,he,Or.inl ⟨rfl,rfl⟩⟩

theorem other_injective : ∀ v : Fin 5, ∀ e f : Fin 10,
    incident v e → incident v f → other v e = other v f → e=f := by decide +kernel

theorem degreeFast_eq (H : Finset (Fin 10)) (v : Fin 5) :
    degreeFast H v = (graph H).degree v := by
  unfold degreeFast
  rw [← card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun e _ => other v e)
  · intro e he
    rcases Finset.mem_filter.mp he with ⟨hmem,hv⟩
    rw [mem_neighborFinset]
    rcases hv with hv|hv
    · subst v
      simpa [other] using edge_adj hmem
    · subst v
      simpa [other, (endpoints_distinct e).symm] using (edge_adj hmem).symm
  · intro e he f hf hef
    exact other_injective v e f (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2 hef
  · intro w hw
    rw [mem_neighborFinset] at hw
    rcases hw with ⟨hne,e,he,h|h⟩
    · rcases h with ⟨rfl,rfl⟩
      exact ⟨e,Finset.mem_filter.mpr ⟨he,Or.inl rfl⟩,by simp [other]⟩
    · rcases h with ⟨rfl,rfl⟩
      exact ⟨e,Finset.mem_filter.mpr ⟨he,Or.inr rfl⟩,
        by simp [other,(endpoints_distinct e).symm]⟩

def prune (H : Finset (Fin 10)) : Finset (Fin 10) :=
  H.filter fun e => 1 < degreeFast H (edgeLo e) ∧ 1 < degreeFast H (edgeHi e)

def cycleCore (H : Finset (Fin 10)) : Finset (Fin 10) := prune (prune H)

def NoIsolated (H : Finset (Fin 10)) : Prop := ∀ v : Fin 5, 0 < degreeFast H v
instance noIsolated_decidable (H : Finset (Fin 10)) : Decidable (NoIsolated H) :=
  inferInstanceAs (Decidable (∀ v : Fin 5, 0 < degreeFast H v))

def Crosses (H : Finset (Fin 10)) (S : Finset (Fin 5)) : Prop :=
  ∃ e ∈ H, (edgeLo e ∈ S ∧ edgeHi e ∉ S) ∨ (edgeHi e ∈ S ∧ edgeLo e ∉ S)
instance crosses_decidable (H : Finset (Fin 10)) (S : Finset (Fin 5)) : Decidable (Crosses H S) :=
  inferInstanceAs (Decidable (∃ e ∈ H,
    (edgeLo e ∈ S ∧ edgeHi e ∉ S) ∨ (edgeHi e ∈ S ∧ edgeLo e ∉ S)))

def cutCheck (H : Finset (Fin 10)) : Bool := decide (NoIsolated H →
  ∀ S ∈ (Finset.univ : Finset (Fin 5)).powerset,
    S.Nonempty → S ≠ Finset.univ → Crosses H S)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cut_finite_check : fiveEdgeList.all cutCheck = true := by kernel_rfl

theorem connected_degree_pos {H : Finset (Fin 10)} (hH : (graph H).Connected) (v : Fin 5) :
    0 < degreeFast H v := by
  rw [degreeFast_eq]
  obtain ⟨w,hw⟩ := exists_ne v
  obtain ⟨p⟩ := hH v w
  cases p with
  | nil => exact (hw rfl).elim
  | cons h p => exact ((graph H).degree_pos_iff_exists_adj v).mpr ⟨_,h⟩

theorem connected_of_cuts {H : Finset (Fin 10)}
    (hc : ∀ S : Finset (Fin 5), S.Nonempty → S ≠ Finset.univ → Crosses H S) :
    (graph H).Connected := by
  classical
  apply (graph H).connected_iff_exists_forall_reachable.mpr
  refine ⟨0,fun w => ?_⟩
  by_contra hw
  let S := Finset.univ.filter fun v => (graph H).Reachable 0 v
  have h0 : (0 : Fin 5) ∈ S := by
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨.nil⟩
  have hSw : w ∉ S := by simpa [S] using hw
  have hne : S ≠ Finset.univ := by intro h; exact hSw (h ▸ Finset.mem_univ w)
  obtain ⟨e,he,hcross⟩ := hc S ⟨0,h0⟩ hne
  have ha := (edge_adj he).reachable
  rcases hcross with h|h
  · apply h.2
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and] at h ⊢
    exact h.1.trans ha
  · apply h.2
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and] at h ⊢
    exact h.1.trans ha.symm

theorem connected_iff_noIsolated {H : Finset (Fin 10)} (hcard : H.card=5) :
    (graph H).Connected ↔ NoIsolated H := by
  refine ⟨connected_degree_pos,fun hn => connected_of_cuts (fun S hS hp => ?_)⟩
  have hm : H ∈ fiveEdgeGraphs := by simp [fiveEdgeGraphs,hcard]
  have hh := List.all_eq_true.mp cut_finite_check H (by
    rw [← List.mem_toFinset, fiveEdgeList_toFinset]
    exact hm)
  exact of_decide_eq_true hh hn S (Finset.mem_powerset.mpr (Finset.subset_univ _)) hS hp

end D4.PrincipalGraphs
