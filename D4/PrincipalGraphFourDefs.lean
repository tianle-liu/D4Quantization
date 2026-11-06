import D4.PrincipalGraphBasics
import D4.PrincipalTreeCertificates

namespace D4.PrincipalGraphs
open SimpleGraph Principal Matrix

def fourEdgeGraphs : Finset (Finset (Fin 10)) := Finset.univ.powersetCard 4

def fourEdgeList : List (Finset (Fin 10)) :=
  ((List.finRange 10).sublistsLen 4).map List.toFinset

theorem fourEdgeList_toFinset : fourEdgeList.toFinset = fourEdgeGraphs := by
  ext H
  simp only [fourEdgeList, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨l,hl,rfl⟩
    rcases List.mem_sublistsLen.mp hl with ⟨hs,hlen⟩
    have hn := (List.nodup_finRange 10).sublist hs
    simpa [fourEdgeGraphs, List.toFinset_card_of_nodup hn] using hlen
  · intro hH
    have hc : H.card=4 := by simpa [fourEdgeGraphs] using hH
    refine ⟨H.sort (· ≤ ·), List.mem_sublistsLen.mpr ⟨?_, ?_⟩, Finset.sort_toFinset _ _⟩
    · exact List.sublist_of_subperm_of_sorted
        (List.subperm_of_subset (Finset.sort_nodup _ _) (fun e _ => List.mem_finRange e))
        (Finset.sort_sorted _ _) (List.pairwise_le_finRange 10)
    · simpa only [Finset.length_sort] using hc

def AllCuts (H : Finset (Fin 10)) : Prop :=
  ∀ S : Finset (Fin 5), S.Nonempty → S ≠ Finset.univ → Crosses H S

instance (H : Finset (Fin 10)) : Decidable (AllCuts H) :=
  inferInstanceAs (Decidable (∀ S : Finset (Fin 5), S.Nonempty → S ≠ Finset.univ → Crosses H S))

theorem connected_iff_allCuts (H : Finset (Fin 10)) : (graph H).Connected ↔ AllCuts H := by
  refine ⟨?_,connected_of_cuts⟩
  intro h S hS hp
  obtain ⟨v,hv⟩ := hS
  obtain ⟨w,hw⟩ : ∃ w : Fin 5, w ∉ S := by
    by_contra hn
    push_neg at hn
    exact hp (Finset.eq_univ_iff_forall.mpr hn)
  by_contra hc
  have hclosed : ∀ u v : Fin 5, u ∈ S → (graph H).Adj u v → v ∈ S := by
    intro u v hu ha
    by_contra hv'
    apply hc
    rcases ha with ⟨hne,e,he,ha|ha⟩
    · rcases ha with ⟨rfl,rfl⟩
      exact ⟨e,he,Or.inl ⟨hu,hv'⟩⟩
    · rcases ha with ⟨rfl,rfl⟩
      exact ⟨e,he,Or.inr ⟨hu,hv'⟩⟩
  have hwalk : ∀ {u v : Fin 5}, (graph H).Walk u v → u ∈ S → v ∈ S := by
    intro u v p
    induction p with
    | nil => exact id
    | cons ha p ih => exact fun hu => ih (hclosed _ _ hu ha)
  obtain ⟨p⟩ := h v w
  exact hw (hwalk p hv)

def treeEdgeSet (t : Fin 125) : Finset (Fin 10) := Finset.univ.image (treeEdges t)

theorem treeEdgeSet_card (t : Fin 125) : (treeEdgeSet t).card=4 := by
  rw [treeEdgeSet, Finset.card_image_of_injective _ (treeEdges_injective t)]
  simp

def minorEdges (H : Finset (Fin 10)) (j : Fin 4) : Fin 10 :=
  (((List.finRange 10).filter fun e => decide (e ∈ H))[j.val]?).getD 0

def canonicalMinor (H : Finset (Fin 10)) : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => integerGenerators (minorEdges H j) i

def fourCheck (H : Finset (Fin 10)) : Bool := decide (
  (Finset.univ.image (minorEdges H) = H) ∧
  (AllCuts H ↔ ∃ t : Fin 125, treeEdgeSet t=H) ∧
  (AllCuts H ↔ (canonicalMinor H).det ≠ 0) ∧
  ((canonicalMinor H).det=0 ∨ (canonicalMinor H).det=1 ∨ (canonicalMinor H).det = -1))

end D4.PrincipalGraphs
