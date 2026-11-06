import D4.C2CellData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal
theorem c2_facet_masks_bounded : ∀ f, c2FacetMask f < 2^120 := by decide +kernel
theorem c2_facet_masks_injective : Function.Injective c2FacetMask := by decide +kernel
theorem c2_facet_normals_ne_zero : ∀ f, c2FacetNormal f ≠ 0 := by decide +kernel
theorem c2_cell_keys_increasing : ∀ i : Fin 579,
    cellKey (c2Cell i.castSucc) < cellKey (c2Cell i.succ) := by decide +kernel
theorem c2_cell_apices : ∀ t,
    (c2Cell t).p = c2FacetApex (c2Cell t).f ∧
    (c2Cell t).q = c2FaceApex (c2Cell t).f (c2Cell t).g := by decide +kernel
theorem c2_cell_incidence : ∀ t,
    OnMask c2FacetMask (c2Cell t).f (c2Cell t).p ∧
    OnMask c2FacetMask (c2Cell t).f (c2Cell t).q ∧
    OnMask c2FacetMask (c2Cell t).f (c2Cell t).u ∧
    OnMask c2FacetMask (c2Cell t).f (c2Cell t).v ∧
    ¬OnMask c2FacetMask (c2Cell t).g (c2Cell t).p ∧
    OnMask c2FacetMask (c2Cell t).g (c2Cell t).q ∧
    OnMask c2FacetMask (c2Cell t).g (c2Cell t).u ∧
    OnMask c2FacetMask (c2Cell t).g (c2Cell t).v ∧
    ¬OnMask c2FacetMask (c2Cell t).h (c2Cell t).q ∧
    OnMask c2FacetMask (c2Cell t).h (c2Cell t).u ∧
    OnMask c2FacetMask (c2Cell t).h (c2Cell t).v := by decide +kernel
end D4.Secondary
