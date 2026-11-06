import D4.PrincipalTreeGeometry
import D4.PrincipalTreeWeights
import D4.PrincipalBoundary

/-! The genuine principal moment equals the sum of the 125 explicitly
integrated tiles. The remaining reduction to the short article polynomial
is a separate finite polynomial certificate. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

def treeMomentNumerator (w : Fin 10 → ℝ) : ℝ :=
  ∑ t : Fin 125, treeWeight w t *
    (3 * quadratic (principalForm w).adjugate (signedCenter w (realTreeSign t)) +
      ∑ j : Fin 4, w (treeEdges t j)^2 *
        quadratic (principalForm w).adjugate (cone1Vectors (treeEdges t j)))

theorem treeTile_volume_sum (w : Fin 10 → ℝ) (hw : ∀ e, 0 < w e) :
    (∑ t : Fin 125, volume (treeTile w t)) = volume (zonotope w) := by
  simp_rw [treeTile_volume w hw]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ =>
    mul_nonneg (by norm_num) (Finset.prod_nonneg (fun j _ => (hw (treeEdges t j)).le)))]
  rw [← Finset.mul_sum]
  change ENNReal.ofReal (16 * ∑ t, treeWeight w t) = _
  rw [sum_treeWeight, zonotope_volume (fun e => (hw e).le) (principal_posDef_of_pos hw)]

theorem zonotope_quadratic_eq_tree_sum (w : Fin 10 → ℝ) (hw : ∀ e, 0 < w e)
    {Q : Gram} (hQ : Q.IsHermitian) :
    (∫ r in zonotope w, quadratic Q r) =
      ∑ t : Fin 125, 16 * treeWeight w t *
        (quadratic Q (signedCenter w (realTreeSign t)) +
          (∑ j : Fin 4, w (treeEdges t j)^2 * quadratic Q (cone1Vectors (treeEdges t j))) / 3) := by
  rw [integral_zonotope_eq_sum_upperTiles realTreeHeight w realTreeNormal
    realTreeNormal_injective (treeTile_volume_sum w hw) _ (quadratic_continuous Q)]
  apply Finset.sum_congr rfl
  intro t _
  exact treeTile_quadratic w hw t hQ

/-- The tree numerator is proved directly from the infinite-nearest-point
integral. No cone moment polynomial is a hypothesis. -/
theorem treeMomentNumerator_eq_actual (w : Fin 10 → ℝ) (hw : ∀ e, 0 < w e) :
    treeMomentNumerator w = 12 * (principalForm w).det^2 * moment (principalForm w) := by
  have hQ := principal_posDef_of_pos hw
  have hscale : (∫ r in zonotope w, quadratic (principalForm w).adjugate r) =
      (16 : ℝ) / 3 * treeMomentNumerator w := by
    rw [zonotope_quadratic_eq_tree_sum w hw (principal_isHermitian w).adjugate,
      treeMomentNumerator, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [zonotope_adjugate_moment (fun e => (hw e).le) hQ] at hscale
  nlinarith

end D4.Principal
