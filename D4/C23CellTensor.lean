import D4.C23CellPolynomials

noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal Certificate

def cellVector (V : Fin 120 → Vec) (c : SecondaryCell) : Fin 4 → Vec :=
  ![V c.p,V c.q,V c.u,V c.v]

def cellVertexPoly (V : Fin 120 → Fin 10 → IntVec) (c : SecondaryCell)
    (l i : Fin 4) : Poly :=
  linearPoly fun k => ![V c.p,V c.q,V c.u,V c.v] l k i

def cellSumPoly (V : Fin 120 → Fin 10 → IntVec) (c : SecondaryCell) (i : Fin 4) : Poly :=
  linearPoly fun k => ∑ l : Fin 4, ![V c.p,V c.q,V c.u,V c.v] l k i

def cellHessianPoly (V : Fin 120 → Fin 10 → IntVec) (c : SecondaryCell)
    (i j : Fin 4) : Poly :=
  mergeAdd (mulMerge (cellSumPoly V c i) (cellSumPoly V c j))
    (sumFast (List.ofFn fun l : Fin 4 => mulMerge (cellVertexPoly V c l i) (cellVertexPoly V c l j)))

def cellHessian (V : Fin 120 → Vec) (c : SecondaryCell) (i j : Fin 4) : ℝ :=
  (∑ l, cellVector V c l i) * (∑ l, cellVector V c l j) +
    ∑ l, cellVector V c l i * cellVector V c l j

def cellTensorPart {n : Nat} (V : Fin 120 → Fin 10 → IntVec) (c : Fin n → SecondaryCell)
    (D : Fin n → Poly) (ts : List (Fin n)) (i j : Fin 4) : Poly :=
  sumFast (ts.map fun t => mulMerge (D t) (cellHessianPoly V (c t) i j))

theorem cellVertexPoly_eval (V : Fin 120 → Fin 10 → IntVec) (c : SecondaryCell)
    (w : Fin 10 → ℝ) (l i : Fin 4) :
    eval (extendWeight w) (cellVertexPoly V c l i) =
      cellVector (secondaryVertex V w) c l i := by
  rw [cellVertexPoly,linearPoly_eval]
  fin_cases l <;> rfl

theorem cellSumPoly_eval (V : Fin 120 → Fin 10 → IntVec) (c : SecondaryCell)
    (w : Fin 10 → ℝ) (i : Fin 4) :
    eval (extendWeight w) (cellSumPoly V c i) =
      ∑ l, cellVector (secondaryVertex V w) c l i := by
  rw [cellSumPoly,linearPoly_eval]
  simp only [Int.cast_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  fin_cases l <;> rfl

theorem cellHessianPoly_eval (V : Fin 120 → Fin 10 → IntVec) (c : SecondaryCell)
    (w : Fin 10 → ℝ) (i j : Fin 4) :
    eval (extendWeight w) (cellHessianPoly V c i j) = cellHessian (secondaryVertex V w) c i j := by
  simp only [cellHessianPoly,eval_mergeAdd,eval_mulMerge,cellSumPoly_eval,
    eval_sumFast,List.map_ofFn,List.sum_ofFn,Function.comp_apply,cellVertexPoly_eval,cellHessian]

theorem cellTensorPart_eval {n : Nat} (V : Fin 120 → Fin 10 → IntVec) (c : Fin n → SecondaryCell)
    (D : Fin n → Poly) (ts : List (Fin n)) (w : Fin 10 → ℝ) (i j : Fin 4) :
    eval (extendWeight w) (cellTensorPart V c D ts i j) =
      (ts.map fun t => eval (extendWeight w) (D t) * cellHessian (secondaryVertex V w) (c t) i j).sum := by
  simp only [cellTensorPart,eval_sumFast,List.map_map,Function.comp_def,
    eval_mulMerge,cellHessianPoly_eval]

end D4.Secondary
