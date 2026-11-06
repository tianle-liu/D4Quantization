import D4.PrincipalGraphBasics

namespace D4.PrincipalGraphs
open SimpleGraph

def edgePair (e : Fin 10) : Sym2 (Fin 5) := Sym2.mk (edgeLo e,edgeHi e)

theorem edgePair_injective : Function.Injective edgePair := by
  have h : ∀ e f : Fin 10, edgePair e = edgePair f → e=f := by decide +kernel
  exact h

theorem graph_edgeFinset (C : Finset (Fin 10)) :
    (graph C).edgeFinset = C.image edgePair := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [mem_edgeFinset,mem_edgeSet,Finset.mem_image]
    constructor
    · rintro ⟨hne,e,he,h|h⟩
      · exact ⟨e,he,by rcases h with ⟨rfl,rfl⟩; rfl⟩
      · exact ⟨e,he,by rcases h with ⟨rfl,rfl⟩; exact Sym2.eq_swap⟩
    · rintro ⟨e,he,heq⟩
      have ha : Sym2.mk (u,v) ∈ (graph C).edgeSet := by
        rw [← heq]
        exact edge_adj he
      exact ha

theorem graph_edge_card (C : Finset (Fin 10)) : (graph C).edgeFinset.card = C.card := by
  rw [graph_edgeFinset,Finset.card_image_of_injective _ edgePair_injective]

end D4.PrincipalGraphs
