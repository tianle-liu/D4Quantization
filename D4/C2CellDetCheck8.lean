import D4.C2CellDetData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2_support_rows_8 : ∀ t : Fin 20,
    let i : Fin 580 := ⟨160+t.val, by omega⟩
    (integerSupportRows c2FacetNormal (c2Cell i) (c2DetCoordinate i)).det = c2DetSign i ∧
    (c2DetSign i)^2 = 1 ∧
    (∀ j, 0 ≤ c2DetSign i * (c2VertexCoefficients (c2Cell i).v j (c2DetCoordinate i) -
      c2VertexCoefficients (c2Cell i).u j (c2DetCoordinate i))) ∧
    (∃ j, 0 < c2DetSign i * (c2VertexCoefficients (c2Cell i).v j (c2DetCoordinate i) -
      c2VertexCoefficients (c2Cell i).u j (c2DetCoordinate i))) := by decide +kernel
theorem c2_det_polynomial_8 : ∀ t : Fin 20,
    let i : Fin 580 := ⟨160+t.val, by omega⟩
    cellFactorProduct c2IntegerGenerators c2VertexCoefficients c2FacetNormal
      (c2Cell i) (c2DetCoordinate i) (c2DetSign i) = c2CellDetPoly i := by decide +kernel
end D4.Secondary
