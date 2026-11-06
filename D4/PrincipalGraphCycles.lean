import D4.PrincipalGraphSemantics
import D4.PrincipalGraphActiveCheck
import D4.PrincipalGraphEdges

namespace D4.PrincipalGraphs
open SimpleGraph

theorem cycleEdges_reachable {C : Finset (Fin 10)} (hC : CycleEdges C)
    {v w : Fin 5} (hv : 0 < (graph C).degree v) (hw : 0 < (graph C).degree w) :
    (graph C).Reachable v w := by
  classical
  by_contra hn
  let S := Finset.univ.filter fun u => (graph C).Reachable v u
  have hvS : v ∈ S := by
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨.nil⟩
  have hwS : w ∉ S := by simpa [S] using hn
  have hc := of_decide_eq_true (of_decide_eq_true active_cut_finite_check C) hC S
    (Finset.mem_powerset.mpr (Finset.subset_univ _)) ⟨v,hvS,by rwa [degreeFast_eq]⟩ ⟨w,hwS,by rwa [degreeFast_eq]⟩
  obtain ⟨e,he,hcross⟩ := hc
  have ha := (edge_adj he).reachable
  rcases hcross with h|h
  · apply h.2
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and] at h ⊢
    exact h.1.trans ha
  · apply h.2
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and] at h ⊢
    exact h.1.trans ha.symm

theorem cycleEdges_actual_cycle {C : Finset (Fin 10)} (hC : CycleEdges C) :
    ∃ v : Fin 5, ∃ p : (graph C).Walk v v,
      p.IsCycle ∧ p.toSubgraph.spanningCoe = graph C ∧ p.length = C.card := by
  classical
  obtain ⟨e,he⟩ := hC.1
  let v := edgeLo e
  have hv : 0 < (graph C).degree v :=
    ((graph C).degree_pos_iff_exists_adj v).mpr ⟨edgeHi e,edge_adj he⟩
  have hc := cycleEdges_isCycles hC
  obtain ⟨p,hp,hpverts⟩ := hc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := (graph C).connectedComponentMk v)
      (by simp only [ConnectedComponent.mem_supp_iff,ConnectedComponent.eq]; exact ⟨.nil⟩)
      ⟨edgeHi e,edge_adj he⟩
  have hgraph : p.toSubgraph.spanningCoe = graph C := by
    ext u w
    constructor
    · exact fun h => h.adj_sub
    · intro huw
      apply (hp.adj_toSubgraph_iff_of_isCycles hc ?_ w).mpr huw
      rw [hpverts]
      have hu := ((graph C).degree_pos_iff_exists_adj u).mpr ⟨w,huw⟩
      simpa only [ConnectedComponent.mem_supp_iff,ConnectedComponent.eq] using
        (cycleEdges_reachable hC hv hu).symm
  refine ⟨v,p,hp,hgraph,?_⟩
  have hedges : p.edges.toFinset = (graph C).edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ u w =>
      simp only [List.mem_toFinset,mem_edgeFinset,mem_edgeSet]
      rw [← p.mem_edges_toSubgraph]
      change p.toSubgraph.spanningCoe.Adj u w ↔ (graph C).Adj u w
      rw [hgraph]
  calc
    p.length = p.edges.toFinset.card :=
      (p.length_edges ▸ List.toFinset_card_of_nodup hp.isTrail.edges_nodup).symm
    _ = C.card := by rw [hedges,graph_edge_card]

/-- The core has a genuine simple cycle whose length is the value used in the counts. -/
theorem connected_five_edge_cycle {H : Finset (Fin 10)} (hcard : H.card=5)
    (hH : (graph H).Connected) :
    ∃ v : Fin 5, ∃ p : (graph (cycleCore H)).Walk v v,
      p.IsCycle ∧ p.toSubgraph.spanningCoe = graph (cycleCore H) ∧
      p.length = (cycleCore H).card :=
  cycleEdges_actual_cycle (unique_cycle_core hcard hH).2.1

/-- The three lengths used in the numerical counts exhaust the actual unique cycles. -/
theorem connected_five_edge_cycle_lengths {H : Finset (Fin 10)} (hcard : H.card=5)
    (hH : (graph H).Connected) :
    (cycleCore H).card=3 ∨ (cycleCore H).card=4 ∨ (cycleCore H).card=5 := by
  obtain ⟨v,p,hp,hgraph,hlen⟩ := connected_five_edge_cycle hcard hH
  have hlo := hp.three_le_length
  rw [hlen] at hlo
  have hhi := Finset.card_le_card (unique_cycle_core hcard hH).1
  omega

/-- Any genuine simple cycle subgraph of a connected five-edge graph has this same edge set. -/
theorem connected_five_edge_unique_actual_cycle {H C : Finset (Fin 10)}
    (hcard : H.card=5) (hH : (graph H).Connected) (hCH : C ⊆ H)
    {v : Fin 5} (p : (graph C).Walk v v) (hp : p.IsCycle)
    (heq : p.toSubgraph.spanningCoe = graph C) : C=cycleCore H := by
  have hn : C.Nonempty := by
    cases p with
    | nil => exact (by simpa using hp.three_le_length : False).elim
    | cons ha p => obtain ⟨hne,e,he,hedge⟩ := ha; exact ⟨e,he⟩
  have hc := hp.isCycles_spanningCoe_toSubgraph
  rw [heq] at hc
  exact (unique_cycle_core hcard hH).2.2 C hCH (cycleEdges_of_isCycles hn hc)

end D4.PrincipalGraphs
