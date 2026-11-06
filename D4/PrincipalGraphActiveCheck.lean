import D4.PrincipalGraphCoreDefs

namespace D4.PrincipalGraphs

def activeCutCheck (C : Finset (Fin 10)) : Bool := decide (CycleEdges C →
  ∀ S ∈ (Finset.univ : Finset (Fin 5)).powerset,
    (∃ v ∈ S, 0 < degreeFast C v) →
    (∃ w, w ∉ S ∧ 0 < degreeFast C w) → Crosses C S)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem active_cut_finite_check :
    decide (∀ C : Finset (Fin 10), activeCutCheck C = true) = true := by kernel_rfl

end D4.PrincipalGraphs
