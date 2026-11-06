import D4.CompactMomentFormulas
import D4.PrincipalGraphMoment
import D4.SecondaryClosedMoment

/-! The displayed compact graph formulas for the genuine secondary-cone moments. -/
noncomputable section
namespace D4.CompactMoments
open Certificate CertificateMoments PrincipalGraphs Analytic

def graphPhi (x : Nat → ℝ) : ℝ :=
  (principalForm (fun i => x i)).det * (∑ i : Fin 10, x i) + graphCycleSum x

theorem graphPhi_eq_momentC1 (x : Nat → ℝ) : graphPhi x = eval x momentC1 := by
  rw [momentC1_graph_formula, determinantC1_eval, parameterC1_eval]
  rfl

theorem secondary2_graph_moment (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).PosDef) :
    60*(secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).det *
      moment (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))) =
      5*graphPhi (z2 x) + 2*(x 0)^3 *
        (2*(x 0)^2 + 5*x 0*(x 3+x 4+x 9) +
          10*(x 3*x 4+x 3*x 9+x 4*x 9)) := by
  rw [Secondary.secondary2_closed_formula x hx hQ, momentC2_compact,
    graphPhi_eq_momentC1]

theorem secondary3_compact_moment (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).PosDef) :
    60*(secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).det *
      moment (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))) =
      eval (theta x) momentC2 +
        2*(x 9)^3 * (3*(x 9)^2 - 5*x 9*(x 1+x 2) + 10*x 1*x 2) := by
  rw [Secondary.secondary3_closed_formula x hx hQ, momentC3_compact]

end D4.CompactMoments
