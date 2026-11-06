import D4.C2CellData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal
theorem c2_slack_incidence_20 : ∀ r,
    (OnMask c2FacetMask 20 r → ∀ k,
      integerSlack c2IntegerGenerators c2VertexCoefficients (c2FacetNormal 20) r k = 0) ∧
    (¬OnMask c2FacetMask 20 r →
      0 < integerSlack c2IntegerGenerators c2VertexCoefficients (c2FacetNormal 20) r
        (c2SlackWitness 20 r)) := by decide +kernel
end D4.Secondary
