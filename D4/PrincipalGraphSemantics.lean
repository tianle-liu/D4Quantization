import D4.PrincipalGraphCoreCheck
import Mathlib.Combinatorics.SimpleGraph.Matching

namespace D4.PrincipalGraphs
open SimpleGraph

/-- Every connected five-edge spanning graph has exactly one nonempty cycle
edge set. Degree two characterizes unions of cycles; on five vertices a
nonempty such subgraph can contain only one cycle. -/
theorem unique_cycle_core {H : Finset (Fin 10)} (hcard : H.card=5)
    (hH : (graph H).Connected) :
    cycleCore H ⊆ H ∧ CycleEdges (cycleCore H) ∧
      ∀ C, C ⊆ H → CycleEdges C → C=cycleCore H := by
  have hm : H ∈ fiveEdgeGraphs := by simp [fiveEdgeGraphs, hcard]
  have hh := List.all_eq_true.mp core_finite_check H (by
    rw [← List.mem_toFinset,fiveEdgeList_toFinset]
    exact hm)
  exact coreCheck_spec hh (connected_degree_pos hH)

theorem cycleEdges_isCycles {C : Finset (Fin 10)} (hC : CycleEdges C) :
    (graph C).IsCycles := by
  intro v hv
  have hp := (graph C).degree_pos_iff_exists_adj v |>.mpr hv
  rw [← degreeFast_eq] at hp
  have hd : degreeFast C v = 2 := (hC.2 v).resolve_left (by omega)
  rw [degreeFast_eq] at hd
  simpa only [Set.ncard_eq_toFinset_card', ← neighborFinset_def, card_neighborFinset_eq_degree] using hd

theorem cycleEdges_of_isCycles {C : Finset (Fin 10)} (hn : C.Nonempty)
    (hc : (graph C).IsCycles) : CycleEdges C := by
  refine ⟨hn,fun v => ?_⟩
  by_cases hz : degreeFast C v=0
  · exact Or.inl hz
  · right
    have hp : 0 < (graph C).degree v := by rw [← degreeFast_eq]; omega
    have hdeg := hc (((graph C).degree_pos_iff_exists_adj v).mp hp)
    rw [Set.ncard_eq_toFinset_card', ← neighborFinset_def,
      card_neighborFinset_eq_degree, ← degreeFast_eq] at hdeg
    exact hdeg

end D4.PrincipalGraphs
