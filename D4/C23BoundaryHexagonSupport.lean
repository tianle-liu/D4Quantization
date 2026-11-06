import D4.C23BoundaryHexagonRepresentation
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope

theorem boundary2_weights_nonneg (z : Parameters) (hz : ∀ i, 0 ≤ z i) :
    ∀ e, 0 ≤ boundary2Weights z e := by
  intro e
  fin_cases e
  · exact hz 1
  · exact hz 2
  · exact hz 3
  · exact hz 4
  · exact le_refl 0
  · exact hz 5
  · exact hz 6
  · exact hz 7
  · exact hz 8
  · exact hz 9

theorem boundary2_point_support (z : Parameters) (hz : ∀ i, 0 ≤ z i)
    (L : Plane) (hL : L ∈ hexagon2 (z 3) (z 4) (z 9)) :
    boundary2Point z L ∈ dualRegion (boundary2Form z) := by
  obtain ⟨t,ht,he,_⟩ := boundary2_point_representation z hz L hL
  have hs := zonotope_integer_support (w := boundary2Weights z)
    (boundary2_weights_nonneg z hz) (r := generatorMap t) ⟨t,ht,rfl⟩
  exact he.symm ▸ hs


end D4.C23Local
