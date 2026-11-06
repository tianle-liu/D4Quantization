import D4.PrincipalTreeData
import D4.PrincipalTiling
import D4.KernelCompute

/-! Every finite geometric witness is checked by kernel reduction. -/
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Principal
open Matrix Analytic

theorem treeEdges_injective : ∀ t : Fin 125, Function.Injective (treeEdges t) :=
  by decide +kernel

theorem tree_matrix_det : ∀ t : Fin 125,
    (integerTreeMatrix t).det = 1 ∨ (integerTreeMatrix t).det = -1 :=
  by decide +kernel

theorem tree_inverse_mul : ∀ t : Fin 125,
    treeInverse t * integerTreeMatrix t = 1 := by decide +kernel

theorem tree_mul_inverse : ∀ t : Fin 125,
    integerTreeMatrix t * treeInverse t = 1 := by decide +kernel

theorem tree_cost_zero_iff : ∀ (t : Fin 125) (e : Fin 10),
    treeCost t e = 0 ↔ ∃ j : Fin 4, treeEdges t j = e := by decide +kernel

theorem tree_sign_cost : ∀ (t : Fin 125) (e : Fin 10),
    treeCost t e * treeSign t e = |treeCost t e| := by decide +kernel

theorem tree_sign_sq : ∀ (t : Fin 125) (e : Fin 10),
    treeCost t e ≠ 0 → (treeSign t e)^2 = 1 := by decide +kernel

theorem tree_sign_zero : ∀ (t : Fin 125) (j : Fin 4),
    treeSign t (treeEdges t j) = 0 := by decide +kernel

theorem treeNormal_injective : Function.Injective treeNormal := by decide +kernel

end D4.Principal
