import D4.C23CellTensorBatches

noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal Certificate

theorem cellVolumeParts_eval {n : Nat} (D : Fin n → Poly)
    (batches : List (List (Fin n))) (x : Nat → ℝ) :
    eval x (sumFast (batches.map fun ts => sumFast (ts.map D))) =
      (batches.flatten.map fun t => eval x (D t)).sum := by
  rw [eval_sumFast]
  induction batches with
  | nil => rfl
  | cons ts bs ih =>
    simp only [List.map_cons,List.sum_cons,List.flatten_cons,List.map_append,List.sum_append,
      eval_sumFast,List.map_map,Function.comp_def]
    congr 1
    simpa only [List.map_map,Function.comp_def,eval_sumFast] using ih

theorem cellVolumeFull_eval {n : Nat} (D : Fin n → Poly)
    (batches : List (List (Fin n)))
    (hcover : batches.flatten = List.ofFn (fun t : Fin n => t)) (x : Nat → ℝ) :
    eval x (sumFast (batches.map fun ts => sumFast (ts.map D))) =
      ∑ t, eval x (D t) := by
  rw [cellVolumeParts_eval,hcover,List.map_ofFn,List.sum_ofFn]
  rfl

end D4.Secondary
