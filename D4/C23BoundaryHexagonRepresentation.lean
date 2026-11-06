import D4.C23BoundaryHexagonCoefficients
import D4.C23BoundaryHexagonAffine
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope

theorem boundary2_point_representation (z : Parameters)
    (hz : ∀ i, 0 ≤ z i) (L : Plane) (hL : L ∈ hexagon2 (z 3) (z 4) (z 9)) :
    ∃ t : Fin 10 → ℝ, t ∈ Icc (-(boundary2Weights z)) (boundary2Weights z) ∧
      boundary2Point z L=generatorMap t ∧
      t 0=z 1 ∧ t 1=z 2 ∧ t 5=z 5 ∧ t 6=z 6 ∧ t 7=z 7 ∧ t 8=z 8 := by
  obtain ⟨t,ht,he⟩ := boundary2_coefficients_exist z hz L hL
  refine ⟨t,ht,?_,?_⟩
  · exact (boundary2_point_of_coefficients z L
      (max (-z 9) (max (L 0-2*z 3-z 9) (z 9-L 1)))).trans
        (congrArg (fun u : Fin 10 → ℝ => generatorMap u) he.symm)
  · exact ⟨congrFun he 0,congrFun he 1,congrFun he 5,
      congrFun he 6,congrFun he 7,congrFun he 8⟩

end D4.C23Local
