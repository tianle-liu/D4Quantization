import D4.C3CellData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal
theorem c3_slack_incidence_14 : ∀ r,
    (OnMask c3FacetMask 14 r → ∀ k,
      integerSlack c3IntegerGenerators c3VertexCoefficients (c3FacetNormal 14) r k = 0) ∧
    (¬OnMask c3FacetMask 14 r →
      0 < integerSlack c3IntegerGenerators c3VertexCoefficients (c3FacetNormal 14) r
        (c3SlackWitness 14 r)) := by decide +kernel
end D4.Secondary
