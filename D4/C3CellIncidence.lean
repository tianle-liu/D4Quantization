import D4.C3CellData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal
theorem c3_facet_masks_bounded : ∀ f, c3FacetMask f < 2^120 := by decide +kernel
theorem c3_facet_masks_injective : Function.Injective c3FacetMask := by decide +kernel
theorem c3_facet_normals_ne_zero : ∀ f, c3FacetNormal f ≠ 0 := by decide +kernel
theorem c3_cell_keys_increasing : ∀ i : Fin 581,
    cellKey (c3Cell i.castSucc) < cellKey (c3Cell i.succ) := by decide +kernel
theorem c3_cell_apices : ∀ t,
    (c3Cell t).p = c3FacetApex (c3Cell t).f ∧
    (c3Cell t).q = c3FaceApex (c3Cell t).f (c3Cell t).g := by decide +kernel
theorem c3_cell_incidence : ∀ t,
    OnMask c3FacetMask (c3Cell t).f (c3Cell t).p ∧
    OnMask c3FacetMask (c3Cell t).f (c3Cell t).q ∧
    OnMask c3FacetMask (c3Cell t).f (c3Cell t).u ∧
    OnMask c3FacetMask (c3Cell t).f (c3Cell t).v ∧
    ¬OnMask c3FacetMask (c3Cell t).g (c3Cell t).p ∧
    OnMask c3FacetMask (c3Cell t).g (c3Cell t).q ∧
    OnMask c3FacetMask (c3Cell t).g (c3Cell t).u ∧
    OnMask c3FacetMask (c3Cell t).g (c3Cell t).v ∧
    ¬OnMask c3FacetMask (c3Cell t).h (c3Cell t).q ∧
    OnMask c3FacetMask (c3Cell t).h (c3Cell t).u ∧
    OnMask c3FacetMask (c3Cell t).h (c3Cell t).v := by decide +kernel
end D4.Secondary
