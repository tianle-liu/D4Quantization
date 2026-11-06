import D4.C23BoundaryRectangleArguments
import D4.C23BoundaryRectangleCostRepresentation
import D4.C23BoundaryRectangle
import D4.C23RectangleSaturation
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope

theorem boundary3_zero_cost_sites (z : Parameters) (hz : ∀ i, 0 ≤ z i)
    (hp : ∀ i : Fin 10, i ≠ 9 → 0 < z i)
    (L : Plane) (hL : L ∈ rectangle3 (z 1) (z 2))
    (n : IntVec) (hn : siteCost (boundary3Form z) (boundary3Point z L) n=0) :
    ∃ i : Fin 8, n=sites3 i := by
  obtain ⟨ha,h2,h3,h5,h6,h7,h8⟩ := boundary3_weights_positive z hp
  obtain ⟨ht2,ht3,ht5,ht6,ht7,ht8⟩ := boundary3_coefficients_saturated z L
  exact rectangle_sum_saturated_sites_of_eq (boundary3Form z) (boundary3Point z L)
    (boundary3Weights z) (boundary3Coefficients z L) (z 0) (boundary3_form_explicit z)
    (boundary3_point_representation z L)
    (boundary3_weights_nonneg z hz) (boundary3_coefficients_mem z hz L hL)
    ha h2 h3 h5 h6 h7 h8 ht2 ht3 ht5 ht6 ht7 ht8 n hn

end D4.C23Local
