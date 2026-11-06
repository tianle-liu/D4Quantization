import D4.PrincipalLaplacianSpectralSemantics
import D4.PrincipalGraphTrees
import D4.PrincipalTreeWeights

/-! The actual K₅ Laplacian cofactor and its spanning-tree expansion. -/
noncomputable section
namespace D4.PrincipalSpectrum
open Matrix Principal PrincipalGraphs

theorem liftedForm_delete_root (Q : RealGram) :
    (liftedForm Q).submatrix Fin.succ Fin.succ=Q := by
  ext i j
  simp only [liftedForm,Matrix.submatrix_apply,Matrix.mul_apply,Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [liftIncidence,Fin.sum_univ_succ]
  all_goals simp (config := { implicitDefEqProofs := false }) only [Matrix.cons_val,
    Fin.reduceSucc,Fin.reduceFinMk,mul_zero,mul_one,zero_mul,one_mul,zero_add,add_zero]

theorem weightedLaplacian_delete_root (w : Fin 10 → ℝ) :
    (weightedLaplacian w).submatrix Fin.succ Fin.succ=principalForm w := by
  rw [weightedLaplacian_eq_lifted,liftedForm_delete_root]

theorem spanning_tree_weight_sum (w : Fin 10 → ℝ) :
    (∑ H ∈ spanningTrees,∏ e ∈ H,w e)=(principalForm w).det := by
  classical
  have hw (t : Fin 125) : (∏ e ∈ treeEdgeSet t,w e)=treeWeight w t := by
    rw [treeEdgeSet,Finset.prod_image]
    · rfl
    · intro i hi j hj hij
      exact treeEdges_injective t hij
  rw [spanningTrees_eq_table,Finset.sum_image]
  · simp_rw [hw]
    exact sum_treeWeight w
  · intro i hi j hj hij
    exact treeEdgeSet_injective hij

/-- Matrix-tree identity, with actual graph-theoretic spanning trees and the
actual reduced five-vertex Laplacian. -/
theorem weightedLaplacian_matrix_tree (w : Fin 10 → ℝ) :
    ((weightedLaplacian w).submatrix Fin.succ Fin.succ).det=
      ∑ H ∈ spanningTrees,∏ e ∈ H,w e := by
  rw [weightedLaplacian_delete_root,spanning_tree_weight_sum]

end D4.PrincipalSpectrum
