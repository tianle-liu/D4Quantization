import D4.PrincipalClosedMoment
import D4.PrincipalGraphPolynomial
import D4.PrincipalGraphCycles
import D4.PolynomialDeterminants

/-! The principal-cone graph formula for the actual nearest-lattice-point integral. -/
noncomputable section
namespace D4.PrincipalGraphs
open Certificate CertificateMoments Analytic

theorem parameterC1_eval (x : Nat → ℝ) :
    eval x parameterC1 = ∑ i : Fin 10, x i := by
  norm_num [parameterC1, eval, monomial, Fin.sum_univ_succ]

/-- The graph sum is over actual connected five-edge spanning subgraphs;
its coefficient is the length of the genuine unique cycle minus two. -/
theorem principal_graph_moment_formula (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (principalForm (fun i => x i)).PosDef) :
    12*(principalForm (fun i => x i)).det * moment (principalForm (fun i => x i)) =
      (principalForm (fun i => x i)).det * (∑ i : Fin 10, x i) + graphCycleSum x := by
  rw [Principal.principal_closed_formula x hx hQ, momentC1_graph_formula,
    determinantC1_eval, parameterC1_eval]

/-- The same identity with exactly the ten geometric edge weights as parameters. -/
theorem principal_graph_moment_formula_finite (w : Fin 10 → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hQ : (principalForm w).PosDef) :
    12*(principalForm w).det * moment (principalForm w) =
      (principalForm w).det * (∑ e, w e) +
        ∑ H ∈ fiveEdgeGraphs.filter (fun H => (graph H).Connected),
          ((cycleCore H).card-2:ℝ) * ∏ e ∈ H, w e := by
  rw [Principal.principal_moment_identity w hw hQ, momentC1_graph_formula,
    determinantC1_eval, parameterC1_eval]
  simp only [Principal.extendWeight_fin, graphCycleSum]

end D4.PrincipalGraphs
