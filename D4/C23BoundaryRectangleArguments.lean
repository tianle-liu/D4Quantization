import D4.C23BoundaryRectangle
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope

theorem boundary3_form_explicit (z : Parameters) :
    boundary3Form z=z 0 • gramMatrix ℝ+principalForm (boundary3Weights z) := rfl

theorem boundary3_weights_positive (z : Parameters) (hp : ∀ i : Fin 10,i≠9 → 0<z i) :
    0<z 0 ∧ 0<boundary3Weights z 2 ∧ 0<boundary3Weights z 3 ∧
    0<boundary3Weights z 5 ∧ 0<boundary3Weights z 6 ∧
    0<boundary3Weights z 7 ∧ 0<boundary3Weights z 8 :=
  ⟨hp 0 (by decide),hp 3 (by decide),hp 4 (by decide),hp 5 (by decide),
    hp 6 (by decide),hp 7 (by decide),hp 8 (by decide)⟩

theorem boundary3_coefficients_saturated (z : Parameters) (L : Plane) :
    boundary3Coefficients z L 2=boundary3Weights z 2 ∧
    boundary3Coefficients z L 3=boundary3Weights z 3 ∧
    boundary3Coefficients z L 5= -(boundary3Weights z 5) ∧
    boundary3Coefficients z L 6= -(boundary3Weights z 6) ∧
    boundary3Coefficients z L 7= -(boundary3Weights z 7) ∧
    boundary3Coefficients z L 8= -(boundary3Weights z 8) :=
  by simp (config := { implicitDefEqProofs := false }) [boundary3Coefficients,boundary3Weights]

end D4.C23Local
