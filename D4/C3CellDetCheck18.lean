import D4.C3CellDetData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3_support_rows_18 : ∀ t : Fin 20,
    let i : Fin 582 := ⟨360+t.val, by omega⟩
    (integerSupportRows c3FacetNormal (c3Cell i) (c3DetCoordinate i)).det = c3DetSign i ∧
    (c3DetSign i)^2 = 1 ∧
    (∀ j, 0 ≤ c3DetSign i * (c3VertexCoefficients (c3Cell i).v j (c3DetCoordinate i) -
      c3VertexCoefficients (c3Cell i).u j (c3DetCoordinate i))) ∧
    (∃ j, 0 < c3DetSign i * (c3VertexCoefficients (c3Cell i).v j (c3DetCoordinate i) -
      c3VertexCoefficients (c3Cell i).u j (c3DetCoordinate i))) := by decide +kernel
theorem c3_det_polynomial_18 : ∀ t : Fin 20,
    let i : Fin 582 := ⟨360+t.val, by omega⟩
    cellFactorProduct c3IntegerGenerators c3VertexCoefficients c3FacetNormal
      (c3Cell i) (c3DetCoordinate i) (c3DetSign i) = c3CellDetPoly i := by decide +kernel
end D4.Secondary
