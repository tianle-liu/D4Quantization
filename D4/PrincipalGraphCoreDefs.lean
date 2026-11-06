import D4.PrincipalGraphCounts

namespace D4.PrincipalGraphs

def CycleEdges (C : Finset (Fin 10)) : Prop :=
  C.Nonempty ∧ ∀ v : Fin 5, degreeFast C v = 0 ∨ degreeFast C v = 2

instance cycleEdges_decidable (C : Finset (Fin 10)) : Decidable (CycleEdges C) :=
  inferInstanceAs (Decidable (C.Nonempty ∧ ∀ v : Fin 5,
    degreeFast C v=0 ∨ degreeFast C v=2))

/-- Enumerate exactly the subsets of H by structural list recursion. -/
def subsetList (H : Finset (Fin 10)) : List (Finset (Fin 10)) :=
  (((List.finRange 10).filter fun e => decide (e ∈ H)).sublists).map List.toFinset

theorem mem_subsetList (H C : Finset (Fin 10)) : C ∈ subsetList H ↔ C ⊆ H := by
  simp only [subsetList, List.mem_map, List.mem_sublists]
  constructor
  · rintro ⟨l,hl,rfl⟩ e he
    have hm := List.mem_filter.mp (hl.subset (List.mem_toFinset.mp he))
    exact of_decide_eq_true hm.2
  · intro hC
    refine ⟨((List.finRange 10).filter fun e => decide (e ∈ H)).filter
      (fun e => decide (e ∈ C)), List.filter_sublist, ?_⟩
    ext e
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq]
    exact ⟨And.right, fun he => ⟨hC he,he⟩⟩

def coreCheck (H : Finset (Fin 10)) : Bool :=
  if NoIsolated H then
    decide (cycleCore H ⊆ H ∧ CycleEdges (cycleCore H)) &&
      (subsetList H).all (fun C => decide (CycleEdges C → C=cycleCore H))
  else true

theorem coreCheck_spec {H : Finset (Fin 10)} (hh : coreCheck H = true)
    (hn : NoIsolated H) :
    cycleCore H ⊆ H ∧ CycleEdges (cycleCore H) ∧
      ∀ C, C ⊆ H → CycleEdges C → C=cycleCore H := by
  have hh' : (decide (cycleCore H ⊆ H ∧ CycleEdges (cycleCore H)) &&
      (subsetList H).all (fun C => decide (CycleEdges C → C=cycleCore H))) = true := by
    simpa only [coreCheck, if_pos hn] using hh
  obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp hh'
  exact ⟨(of_decide_eq_true h₁).1,(of_decide_eq_true h₁).2,
    fun C hC => of_decide_eq_true (List.all_eq_true.mp h₂ C ((mem_subsetList H C).mpr hC))⟩

end D4.PrincipalGraphs
