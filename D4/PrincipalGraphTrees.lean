import D4.PrincipalGraphFourCheck
import D4.PrincipalGraphEdges
import D4.PrincipalGraphIncidence
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace D4.PrincipalGraphs
open SimpleGraph

theorem four_facts {H : Finset (Fin 10)} (hH : H.card=4) :
    (Finset.univ.image (minorEdges H) = H) ∧
    (AllCuts H ↔ ∃ t : Fin 125, treeEdgeSet t=H) ∧
    (AllCuts H ↔ (canonicalMinor H).det ≠ 0) ∧
    ((canonicalMinor H).det=0 ∨ (canonicalMinor H).det=1 ∨ (canonicalMinor H).det = -1) := by
  have hm : H ∈ fourEdgeGraphs := by simp [fourEdgeGraphs,hH]
  have hh := List.all_eq_true.mp four_finite_check H (by
    rw [← List.mem_toFinset,fourEdgeList_toFinset]
    exact hm)
  exact of_decide_eq_true hh

theorem isTree_card {H : Finset (Fin 10)} (hH : (graph H).IsTree) : H.card=4 := by
  have hc := hH.card_edgeFinset
  rw [graph_edge_card] at hc
  norm_num at hc
  omega

theorem treeEdgeSet_isTree (t : Fin 125) : (graph (treeEdgeSet t)).IsTree := by
  apply (isTree_iff_connected_and_card (G := graph (treeEdgeSet t))).mpr
  refine ⟨(connected_iff_allCuts _).mpr
    ((four_facts (treeEdgeSet_card t)).2.1.mpr ⟨t,rfl⟩), ?_⟩
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, graph_edge_card, treeEdgeSet_card]
  norm_num

/-- The 125-entry table exhausts the actual labelled spanning trees of K₅. -/
theorem isTree_iff_table (H : Finset (Fin 10)) :
    (graph H).IsTree ↔ ∃ t : Fin 125, treeEdgeSet t=H := by
  constructor
  · intro hH
    exact (four_facts (isTree_card hH)).2.1.mp
      ((connected_iff_allCuts H).mp hH.isConnected)
  · rintro ⟨t,rfl⟩
    exact treeEdgeSet_isTree t

noncomputable def spanningTrees : Finset (Finset (Fin 10)) := by
  classical
  exact Finset.univ.filter fun H => (graph H).IsTree

theorem spanningTrees_eq_table : spanningTrees = Finset.univ.image treeEdgeSet := by
  classical
  ext H
  simp only [spanningTrees, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image, isTree_iff_table]

/-- This counts actual graph-theoretic spanning trees, with no enumeration premise. -/
theorem spanningTrees_card : spanningTrees.card=125 := by
  rw [spanningTrees_eq_table,treeEdgeSets_card]

theorem treeEdgeSet_injective : Function.Injective treeEdgeSet := by
  have hc : (Finset.univ.image treeEdgeSet).card = (Finset.univ : Finset (Fin 125)).card := by
    simpa using treeEdgeSets_card
  exact fun s t h => (Finset.card_image_iff.mp hc)
    (Finset.mem_univ s) (Finset.mem_univ t) h

theorem canonicalMinor_columns {H : Finset (Fin 10)} (hH : H.card=4) :
    Finset.univ.image (minorEdges H) = H := (four_facts hH).1

theorem canonicalMinor_nonzero_iff_connected {H : Finset (Fin 10)} (hH : H.card=4) :
    (canonicalMinor H).det ≠ 0 ↔ (graph H).Connected :=
  (four_facts hH).2.2.1.symm.trans (connected_iff_allCuts H).symm

/-- Among all four-column reduced-incidence minors, precisely the spanning-tree minors are nonzero. -/
theorem canonicalMinor_nonzero_iff_isTree {H : Finset (Fin 10)} (hH : H.card=4) :
    (canonicalMinor H).det ≠ 0 ↔ (graph H).IsTree :=
  (four_facts hH).2.2.1.symm.trans ((four_facts hH).2.1.trans (isTree_iff_table H).symm)

theorem canonicalMinor_nonzero_value {H : Finset (Fin 10)} (hH : H.card=4)
    (hn : (canonicalMinor H).det ≠ 0) :
    (canonicalMinor H).det=1 ∨ (canonicalMinor H).det = -1 :=
  (four_facts hH).2.2.2.resolve_left hn

noncomputable def nonzeroMinors : Finset (Finset (Fin 10)) :=
  fourEdgeGraphs.filter fun H => (canonicalMinor H).det ≠ 0

theorem nonzeroMinors_eq_spanningTrees : nonzeroMinors = spanningTrees := by
  classical
  ext H
  simp only [nonzeroMinors, spanningTrees, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hc,hn⟩
    have hcard : H.card=4 := by simpa [fourEdgeGraphs] using hc
    exact (canonicalMinor_nonzero_iff_isTree hcard).mp hn
  · intro hH
    have hcard := isTree_card hH
    exact ⟨by simp [fourEdgeGraphs,hcard], (canonicalMinor_nonzero_iff_isTree hcard).mpr hH⟩

theorem nonzeroMinors_card : nonzeroMinors.card=125 := by
  rw [nonzeroMinors_eq_spanningTrees,spanningTrees_card]

/-- The assertion for the reduced incidence matrix itself, including the source sign convention. -/
theorem incidenceMinor_nonzero_iff_connected {H : Finset (Fin 10)} (hH : H.card=4) :
    (incidenceMinor H).det ≠ 0 ↔ (graph H).Connected :=
  (canonicalMinor_nonzero_iff_incidence H).symm.trans
    (canonicalMinor_nonzero_iff_connected hH)

theorem incidenceMinor_abs_det_eq_one {H : Finset (Fin 10)}
    (hH : H.card=4) (hc : (graph H).Connected) : |(incidenceMinor H).det|=1 := by
  rw [← canonicalMinor_abs_det_eq_incidence]
  rcases canonicalMinor_nonzero_value hH ((canonicalMinor_nonzero_iff_connected hH).mpr hc) with h|h
  · rw [h]; norm_num
  · rw [h]; norm_num

end D4.PrincipalGraphs
