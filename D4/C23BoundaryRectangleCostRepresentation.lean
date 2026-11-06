import D4.C23BoundaryRectangle
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope

theorem boundary3_point_cost_representation (z : Parameters) (L : Plane) (n : IntVec) :
    siteCost (boundary3Form z) (boundary3Point z L) n =
      siteCost (z 0 • gramMatrix ℝ+principalForm (boundary3Weights z))
        (z 0 • (![-2,-2,2,2] : Vec)+generatorMap (boundary3Coefficients z L)) n :=
  congrArg (fun r => siteCost (boundary3Form z) r n) (boundary3_point_representation z L)

end D4.C23Local
