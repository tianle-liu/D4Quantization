import D4.C2CellData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal
theorem c2_slack_incidence_6 : ∀ r,
    (OnMask c2FacetMask 6 r → ∀ k,
      integerSlack c2IntegerGenerators c2VertexCoefficients (c2FacetNormal 6) r k = 0) ∧
    (¬OnMask c2FacetMask 6 r →
      0 < integerSlack c2IntegerGenerators c2VertexCoefficients (c2FacetNormal 6) r
        (c2SlackWitness 6 r)) := by decide +kernel
end D4.Secondary
