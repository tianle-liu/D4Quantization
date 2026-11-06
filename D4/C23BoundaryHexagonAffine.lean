import D4.C23BoundaryHexagonData
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope
set_option maxHeartbeats 200000

theorem boundary2_point_of_coefficients (z : Parameters) (L : Plane) (k : ℝ) :
    boundary2Point z L=generatorMap
      (![z 1,z 2,L 0-z 3-z 9-k,L 1-z 4-z 9+k,0,z 5,z 6,z 7,z 8,k] : Fin 10 → ℝ) := by
  have hcoords := generatorMap_coordinates
    (![z 1,z 2,L 0-z 3-z 9-k,L 1-z 4-z 9+k,0,z 5,z 6,z 7,z 8,k] : Fin 10 → ℝ)
  refine Eq.trans ?_ hcoords.symm
  unfold boundary2Point
  rw [boundary2_matrix]
  ext i
  fin_cases i
  · change z 1+z 5+z 6=z 1+0+z 5+z 6; ring
  · change z 2+z 7+z 8=z 2-0+z 7+z 8; ring
  · change L 0-(z 3+z 5+z 7+z 9)=(L 0-z 3-z 9-k)-z 5-z 7+k; ring
  · change L 1-(z 4+z 6+z 8+z 9)=(L 1-z 4-z 9+k)-z 6-z 8-k; ring

end D4.C23Local
