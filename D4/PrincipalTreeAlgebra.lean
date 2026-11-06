import D4.PrincipalTreeAdjugate
import D4.PrincipalTiles

/-! Semantic bridge from the executable sparse polynomial operations to the
actual centers and second-moment tensors of the 125 parallelotopes. -/
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Principal
open Matrix Analytic Certificate
noncomputable section

def centerPoly (t : Fin 125) (i : Fin 4) : Poly :=
  normalize (List.ofFn fun e : Fin 10 =>
    ([e.val], treeSign t e * integerGenerators e i))

def edgeSquarePoly (t : Fin 125) (i j : Fin 4) : Poly :=
  normalize (List.ofFn fun k : Fin 4 =>
    ([(treeEdges t k).val, (treeEdges t k).val],
      integerGenerators (treeEdges t k) i * integerGenerators (treeEdges t k) j))

def hessianPoly (t : Fin 125) (i j : Fin 4) : Poly :=
  mergeAdd (scale 3 (mul (centerPoly t i) (centerPoly t j))) (edgeSquarePoly t i j)

def treeMono (t : Fin 125) : Poly :=
  [(List.ofFn fun k : Fin 4 => (treeEdges t k).val, 1)]

def tensorRaw (i j : Fin 4) : Poly :=
  sumFast (List.ofFn fun t : Fin 125 => mul (treeMono t) (hessianPoly t i j))

def treeCenter (w : Fin 10 → ℝ) (t : Fin 125) : Vec :=
  signedCenter w (fun e => (treeSign t e : ℝ))

def treeHessian (w : Fin 10 → ℝ) (t : Fin 125) (i j : Fin 4) : ℝ :=
  3 * treeCenter w t i * treeCenter w t j +
    ∑ k, w (treeEdges t k)^2 * cone1Vectors (treeEdges t k) i * cone1Vectors (treeEdges t k) j

def treeTensor (w : Fin 10 → ℝ) (i j : Fin 4) : ℝ :=
  ∑ t, treeWeight w t * treeHessian w t i j

theorem centerPoly_eval (w : Fin 10 → ℝ) (t : Fin 125) (i : Fin 4) :
    eval (extendWeight w) (centerPoly t i) = treeCenter w t i := by
  rw [centerPoly, eval_normalize]
  simp only [eval, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, Int.cast_mul, generators_cast, monomial,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, extendWeight_fin]
  simp only [treeCenter, signedCenter, generatorMap, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem edgeSquarePoly_eval (w : Fin 10 → ℝ) (t : Fin 125) (i j : Fin 4) :
    eval (extendWeight w) (edgeSquarePoly t i j) =
      ∑ k, w (treeEdges t k)^2 * cone1Vectors (treeEdges t k) i * cone1Vectors (treeEdges t k) j := by
  rw [edgeSquarePoly, eval_normalize]
  simp only [eval, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, Int.cast_mul, generators_cast, monomial,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, extendWeight_fin]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem hessianPoly_eval (w : Fin 10 → ℝ) (t : Fin 125) (i j : Fin 4) :
    eval (extendWeight w) (hessianPoly t i j) = treeHessian w t i j := by
  simp only [hessianPoly, eval_mergeAdd, eval_scale, eval_mul,
    centerPoly_eval, edgeSquarePoly_eval, treeHessian, Int.cast_ofNat]
  ring

theorem treeMono_eval (w : Fin 10 → ℝ) (t : Fin 125) :
    eval (extendWeight w) (treeMono t) = treeWeight w t := by
  simp only [treeMono, eval_cons, eval_nil, Int.cast_one, one_mul, add_zero,
    monomial, List.map_ofFn, List.prod_ofFn, Function.comp_apply, extendWeight_fin, treeWeight]

theorem tensorRaw_eval (w : Fin 10 → ℝ) (i j : Fin 4) :
    eval (extendWeight w) (tensorRaw i j) = treeTensor w i j := by
  simp only [tensorRaw, eval_sumFast, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, eval_mul, treeMono_eval, hessianPoly_eval, treeTensor]

theorem treeTensor_symmetric (w : Fin 10 → ℝ) (i j : Fin 4) :
    treeTensor w i j = treeTensor w j i := by
  unfold treeTensor
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  unfold treeHessian
  have hs : (∑ k, w (treeEdges t k)^2 * cone1Vectors (treeEdges t k) i * cone1Vectors (treeEdges t k) j) =
      ∑ k, w (treeEdges t k)^2 * cone1Vectors (treeEdges t k) j * cone1Vectors (treeEdges t k) i := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs]
  ring

end
end D4.Principal
