import D4.C3CellData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal
theorem c3_slack_incidence_2 : ∀ r,
    (OnMask c3FacetMask 2 r → ∀ k,
      integerSlack c3IntegerGenerators c3VertexCoefficients (c3FacetNormal 2) r k = 0) ∧
    (¬OnMask c3FacetMask 2 r →
      0 < integerSlack c3IntegerGenerators c3VertexCoefficients (c3FacetNormal 2) r
        (c3SlackWitness 2 r)) := by decide +kernel
end D4.Secondary
