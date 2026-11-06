import D4.PrincipalTreeCertificates
import D4.PrincipalTiles
import D4.PrincipalMomentTransform

/-! Application of the generic lifted-face construction to all 125 checked
spanning trees. Every geometric hypothesis is discharged by integer data. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

def realTreeHeight : Fin 10 → ℝ := fun e => (treeHeight e : ℝ)
def realTreeNormal (t : Fin 125) : Vec := castVec (treeNormal t)
def realTreeSign (t : Fin 125) : Fin 10 → ℝ := fun e => (treeSign t e : ℝ)

def treeTile (w : Fin 10 → ℝ) (t : Fin 125) : Set Vec :=
  upperTile realTreeHeight w (realTreeNormal t)

theorem treeCost_cast (t : Fin 125) (e : Fin 10) :
    (treeCost t e : ℝ) = reducedCost realTreeHeight (realTreeNormal t) e := by
  simp only [treeCost, reducedCost, realTreeHeight, realTreeNormal, castVec,
    dotProduct, Int.cast_sub, Int.cast_sum, Int.cast_mul, generators_cast]

theorem realTreeNormal_injective : Function.Injective realTreeNormal := by
  intro t s h
  apply treeNormal_injective
  ext i
  exact Int.cast_injective (congrFun h i)

theorem treeTile_eq_parallelotope (w : Fin 10 → ℝ) (hw : ∀ e, 0 < w e) (t : Fin 125) :
    treeTile w t = parallelotope (weightedEdgeMatrix w (treeEdges t))
      (signedCenter w (realTreeSign t)) := by
  apply upperTile_eq_parallelotope _ _ _ _ _ (treeEdges_injective t) hw
  · intro j
    rw [← treeCost_cast]
    exact_mod_cast (tree_cost_zero_iff t (treeEdges t j)).mpr ⟨j, rfl⟩
  · intro e he
    rw [← treeCost_cast]
    exact_mod_cast (fun hz => he ((tree_cost_zero_iff t e).mp hz))
  · intro j
    unfold realTreeSign
    exact_mod_cast tree_sign_zero t j
  · intro e he
    have hn : treeCost t e ≠ 0 := fun hz => he ((tree_cost_zero_iff t e).mp hz)
    have hs : (realTreeSign t e)^2 = 1 := by unfold realTreeSign; exact_mod_cast tree_sign_sq t e hn
    have ha : |realTreeSign t e|^2 = 1 := by rwa [sq_abs]
    nlinarith [abs_nonneg (realTreeSign t e)]
  · intro e
    rw [← treeCost_cast]
    unfold realTreeSign
    exact_mod_cast tree_sign_cost t e

theorem edgeMatrix_tree_abs_det (t : Fin 125) : |(edgeMatrix (treeEdges t)).det| = 1 := by
  have hm : (integerTreeMatrix t).map (Int.castRingHom ℝ) = edgeMatrix (treeEdges t) := by
    ext i j
    exact generators_cast (treeEdges t j) i
  rw [← hm]
  change |((integerTreeMatrix t).map (fun z : ℤ => (z : ℝ))).det| = 1
  rw [← Int.cast_det]
  rcases tree_matrix_det t with hd | hd <;> rw [hd] <;> norm_num

theorem weightedEdgeMatrix_tree_abs_det (w : Fin 10 → ℝ) (hw : ∀ e, 0 < w e) (t : Fin 125) :
    |(weightedEdgeMatrix w (treeEdges t)).det| = ∏ j, w (treeEdges t j) := by
  rw [weightedEdgeMatrix_det, abs_mul, edgeMatrix_tree_abs_det, one_mul,
    abs_of_pos (Finset.prod_pos (fun j _ => hw (treeEdges t j)))]

theorem weightedEdgeMatrix_tree_det_ne_zero (w : Fin 10 → ℝ)
    (hw : ∀ e, 0 < w e) (t : Fin 125) : (weightedEdgeMatrix w (treeEdges t)).det ≠ 0 := by
  apply abs_ne_zero.mp
  rw [weightedEdgeMatrix_tree_abs_det w hw t]
  exact (Finset.prod_pos (fun j _ => hw (treeEdges t j))).ne'

theorem treeTile_volume (w : Fin 10 → ℝ) (hw : ∀ e, 0 < w e) (t : Fin 125) :
    volume (treeTile w t) = ENNReal.ofReal (16 * ∏ j, w (treeEdges t j)) := by
  rw [treeTile_eq_parallelotope w hw t,
    parallelotope_volume _ (weightedEdgeMatrix_tree_det_ne_zero w hw t),
    weightedEdgeMatrix_tree_abs_det w hw t]

theorem treeTile_quadratic (w : Fin 10 → ℝ) (hw : ∀ e, 0 < w e) (t : Fin 125)
    {Q : Gram} (hQ : Q.IsHermitian) :
    (∫ r in treeTile w t, quadratic Q r) =
      16 * (∏ j, w (treeEdges t j)) * (quadratic Q (signedCenter w (realTreeSign t)) +
        (∑ j, w (treeEdges t j)^2 * quadratic Q (cone1Vectors (treeEdges t j))) / 3) := by
  rw [treeTile_eq_parallelotope w hw t,
    parallelotope_quadratic hQ _ (weightedEdgeMatrix_tree_det_ne_zero w hw t),
    weightedEdgeMatrix_tree_abs_det w hw t, trace_weightedEdgeMatrix]

end D4.Principal
