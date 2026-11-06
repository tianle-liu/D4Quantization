import D4.C23BoundaryHexagonSites
import D4.C23BoundaryNearest
import D4.C23BoundaryPosDef
import D4.DualEmbeddedNeighborhood

noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope
attribute [local instance] Matrix.normedAddCommGroup

theorem square2_injective : Function.Injective square2 := by decide
theorem square2_card : (Finset.univ.image square2).card=4 := by
  rw [Finset.card_image_of_injective _ square2_injective]
  simp

theorem boundary2_square_cost (z : Parameters) (L : Plane) (i : Fin 4) :
    siteCost (boundary2Form z) (boundary2Point z L) (square2 i)=0 := by
  fin_cases i <;>
    simp only [square2,Fin.reduceFinMk,Matrix.cons_val,boundary2_point_costs]

theorem boundary2_translate_injective (z : Parameters) (hz : ∀ i,0≤z i)
    (hp : ∀ i : Fin 10,i≠0 → 0<z i) :
    ∀ r∈dualSquareFace (boundary2Form z) 0 1,∀ n : IntVec,
      r+((2:ℝ) • boundary2Form z)*ᵥ(castVec n)∈dualSquareFace (boundary2Form z) 0 1 → n=0 := by
  apply dual_face_translate_injective (boundary2_posDef z hz hp)
    (dualSquareFace (boundary2Form z) 0 1) (fun _ h => h.1)
    (Finset.univ.image square2)
  · intro r hr n hn
    rw [boundary2_dual_face z hz] at hr
    obtain ⟨L,hL,rfl⟩ := hr
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hn
    exact boundary2_square_cost z L i
  · intro r hr
    rw [boundary2_dual_face z hz] at hr
    obtain ⟨L,hL,rfl⟩ := hr
    obtain ⟨T,hcard,hT⟩ := boundary2_at_most_six z hz hp L hL
    refine ⟨T,hT,?_⟩
    rw [square2_card]
    omega

theorem boundary2_embedded_neighborhood (z : Parameters) (hz : ∀ i,0≤z i)
    (hp : ∀ i : Fin 10,i≠0 → 0<z i) :
    ∃ ε : ℝ,0<ε ∧ ∃ U : Set Vec,IsOpen U ∧ dualSquareFace (boundary2Form z) 0 1⊆U ∧
      ∀ R : Gram,‖R-boundary2Form z‖<ε → ∀ x∈U,∀ n : IntVec,
        x+dualMap R (castVec n)∈U → n=0 :=
  compact_dual_embedded_neighborhood (boundary2_posDef z hz hp) _
    (dualSquareFace_compact (boundary2_posDef z hz hp) 0 1)
    (boundary2_translate_injective z hz hp)


end D4.C23Local
