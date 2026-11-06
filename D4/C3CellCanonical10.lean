import D4.C3CellData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal
theorem c3_face_canonical_10 : ∀ t : Fin 20, ∀ g : Fin 30,
    let a := c3Cell ⟨200 + t.val, by omega⟩
    c3FacetMask a.f &&& c3FacetMask g = c3FacetMask a.f &&& c3FacetMask a.g → a.g ≤ g := by decide +kernel
theorem c3_edge_canonical_10 : ∀ t : Fin 20, ∀ h : Fin 30,
    let a := c3Cell ⟨200 + t.val, by omega⟩
    c3FacetMask a.f &&& c3FacetMask a.g &&& c3FacetMask h =
      c3FacetMask a.f &&& c3FacetMask a.g &&& c3FacetMask a.h → a.h ≤ h := by decide +kernel
end D4.Secondary
