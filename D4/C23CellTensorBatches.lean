import D4.C23CellTensor

noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal Certificate

theorem cellTensorParts_eval {n : Nat} (V : Fin 120 → Fin 10 → IntVec)
    (c : Fin n → SecondaryCell) (D : Fin n → Poly) (batches : List (List (Fin n)))
    (w : Fin 10 → ℝ) (i j : Fin 4) :
    eval (extendWeight w) (sumFast (batches.map fun ts => cellTensorPart V c D ts i j)) =
      (batches.flatten.map fun t => eval (extendWeight w) (D t) *
        cellHessian (secondaryVertex V w) (c t) i j).sum := by
  rw [eval_sumFast]
  induction batches with
  | nil => rfl
  | cons ts bs ih =>
    simp only [List.map_cons,List.sum_cons,List.flatten_cons,List.map_append,List.sum_append,
      cellTensorPart_eval]
    rw [ih]

theorem cellTensorFull_eval {n : Nat} (V : Fin 120 → Fin 10 → IntVec)
    (c : Fin n → SecondaryCell) (D : Fin n → Poly) (batches : List (List (Fin n)))
    (hcover : batches.flatten = List.ofFn (fun t : Fin n => t))
    (w : Fin 10 → ℝ) (i j : Fin 4) :
    eval (extendWeight w) (sumFast (batches.map fun ts => cellTensorPart V c D ts i j)) =
      ∑ t, eval (extendWeight w) (D t) * cellHessian (secondaryVertex V w) (c t) i j := by
  rw [cellTensorParts_eval,hcover,List.map_ofFn,List.sum_ofFn]
  rfl

end D4.Secondary
