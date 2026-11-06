import D4.C2CellData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal
theorem c2_face_canonical_5 : ∀ t : Fin 20, ∀ g : Fin 30,
    let a := c2Cell ⟨100 + t.val, by omega⟩
    c2FacetMask a.f &&& c2FacetMask g = c2FacetMask a.f &&& c2FacetMask a.g → a.g ≤ g := by decide +kernel
theorem c2_edge_canonical_5 : ∀ t : Fin 20, ∀ h : Fin 30,
    let a := c2Cell ⟨100 + t.val, by omega⟩
    c2FacetMask a.f &&& c2FacetMask a.g &&& c2FacetMask h =
      c2FacetMask a.f &&& c2FacetMask a.g &&& c2FacetMask a.h → a.h ≤ h := by decide +kernel
end D4.Secondary
