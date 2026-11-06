import D4.C3CellData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal
theorem c3_slack_incidence_29 : ∀ r,
    (OnMask c3FacetMask 29 r → ∀ k,
      integerSlack c3IntegerGenerators c3VertexCoefficients (c3FacetNormal 29) r k = 0) ∧
    (¬OnMask c3FacetMask 29 r →
      0 < integerSlack c3IntegerGenerators c3VertexCoefficients (c3FacetNormal 29) r
        (c3SlackWitness 29 r)) := by decide +kernel
end D4.Secondary
