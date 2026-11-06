import D4.C23BoundaryRectangleCard
import D4.C23BoundaryNearest
import D4.C23BoundaryPosDef
import D4.DualEmbeddedNeighborhood

noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope
attribute [local instance] Matrix.normedAddCommGroup

theorem square3_injective : Function.Injective square3 := by decide

theorem square3_card : (Finset.univ.image square3).card=4 := by
  rw [Finset.card_image_of_injective _ square3_injective]
  simp

theorem boundary3_square_cost (z : Parameters) (L : Plane) (i : Fin 4) :
    siteCost (boundary3Form z) (boundary3Point z L) (square3 i)=0 := by
  fin_cases i <;>
    simp only [square3,Fin.reduceFinMk,Matrix.cons_val,boundary3_point_costs]

theorem boundary3_translate_injective (z : Parameters) (hz : ∀ i,0≤z i)
    (hp : ∀ i : Fin 10,i≠9 → 0<z i) :
    ∀ r∈dualSquareFace (boundary3Form z) 2 3,∀ n : IntVec,
      r+((2:ℝ) • boundary3Form z)*ᵥ(castVec n)∈dualSquareFace (boundary3Form z) 2 3 → n=0 := by
  apply dual_face_translate_injective (boundary3_posDef z hz hp)
    (dualSquareFace (boundary3Form z) 2 3) (fun _ h => h.1)
    (Finset.univ.image square3)
  · intro r hr n hn
    rw [boundary3_dual_face z hz] at hr
    obtain ⟨L,hL,rfl⟩ := hr
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hn
    exact boundary3_square_cost z L i
  · intro r hr
    rw [boundary3_dual_face z hz] at hr
    obtain ⟨L,hL,rfl⟩ := hr
    obtain ⟨T,hcard,hT⟩ := boundary3_at_most_six z hz hp L hL
    refine ⟨T,hT,?_⟩
    rw [square3_card]
    omega


theorem boundary3_embedded_neighborhood (z : Parameters) (hz : ∀ i,0≤z i)
    (hp : ∀ i : Fin 10,i≠9 → 0<z i) :
    ∃ ε : ℝ,0<ε ∧ ∃ U : Set Vec,IsOpen U ∧ dualSquareFace (boundary3Form z) 2 3⊆U ∧
      ∀ R : Gram,‖R-boundary3Form z‖<ε → ∀ x∈U,∀ n : IntVec,
        x+dualMap R (castVec n)∈U → n=0 :=
  compact_dual_embedded_neighborhood (boundary3_posDef z hz hp) _
    (dualSquareFace_compact (boundary3_posDef z hz hp) 2 3)
    (boundary3_translate_injective z hz hp)


end D4.C23Local
