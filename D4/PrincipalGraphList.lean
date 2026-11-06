import D4.KernelCompute
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Tactic
namespace D4.PrincipalGraphs

def fiveEdgeGraphs : Finset (Finset (Fin 10)) := Finset.univ.powersetCard 5

/-- Canonical five-edge subsets enumerated by structural list recursion. -/
def fiveEdgeList : List (Finset (Fin 10)) :=
  ((List.finRange 10).sublistsLen 5).map List.toFinset

theorem fiveEdgeList_nodup : fiveEdgeList.Nodup := by
  apply (List.nodup_sublistsLen 5 (List.nodup_finRange 10)).map_on
  intro a ha b hb hab
  have ha' := (List.mem_sublistsLen.mp ha).1
  have hb' := (List.mem_sublistsLen.mp hb).1
  exact List.eq_of_perm_of_sorted
    (List.perm_of_nodup_nodup_toFinset_eq
      ((List.nodup_finRange 10).sublist ha') ((List.nodup_finRange 10).sublist hb') hab)
    ((List.pairwise_le_finRange 10).sublist ha')
    ((List.pairwise_le_finRange 10).sublist hb')

theorem fiveEdgeList_toFinset : fiveEdgeList.toFinset = fiveEdgeGraphs := by
  ext H
  simp only [fiveEdgeList, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨l,hl,rfl⟩
    rcases List.mem_sublistsLen.mp hl with ⟨hs,hlen⟩
    have hn := (List.nodup_finRange 10).sublist hs
    simpa [fiveEdgeGraphs, List.toFinset_card_of_nodup hn] using hlen
  · intro hH
    have hc : H.card=5 := by simpa [fiveEdgeGraphs] using hH
    refine ⟨H.sort (· ≤ ·), List.mem_sublistsLen.mpr ⟨?_, ?_⟩, Finset.sort_toFinset _ _⟩
    · apply List.sublist_of_subperm_of_sorted
        (List.subperm_of_subset (Finset.sort_nodup _ _) (fun e _ => List.mem_finRange e))
        (Finset.sort_sorted _ _) (List.pairwise_le_finRange 10)
    · simpa only [Finset.length_sort] using hc
end D4.PrincipalGraphs
