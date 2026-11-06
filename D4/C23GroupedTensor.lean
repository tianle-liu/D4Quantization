import D4.C23CellTensorBatches

/-! Exact regrouping of simplex tensors with identical determinant polynomials. -/
noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal Certificate

theorem group_determinants_of_check {ι : Type*} (D : ι → Poly)
    (representative : ι) (ts : List ι)
    (h : ts.all (fun t => decide (D t=D representative))=true) :
    ∀ t∈ts,D t=D representative := by
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp h t ht)

def cellGroupedTensor {n : Nat} (V : Fin 120 → Fin 10 → IntVec)
    (c : Fin n → SecondaryCell) (D : Fin n → Poly)
    (representative : Fin n) (ts : List (Fin n)) (i j : Fin 4) : Poly :=
  mulMerge (D representative) (sumFast (ts.map fun t => cellHessianPoly V (c t) i j))

theorem cellGroupedTensor_eval {n : Nat} (V : Fin 120 → Fin 10 → IntVec)
    (c : Fin n → SecondaryCell) (D : Fin n → Poly)
    (representative : Fin n) (ts : List (Fin n))
    (hD : ∀ t∈ts,D t=D representative) (w : Fin 10 → ℝ) (i j : Fin 4) :
    eval (extendWeight w) (cellGroupedTensor V c D representative ts i j)=
      (ts.map fun t => eval (extendWeight w) (D t)*
        cellHessian (secondaryVertex V w) (c t) i j).sum := by
  rw [cellGroupedTensor,eval_mulMerge,eval_sumFast]
  simp only [List.map_map,Function.comp_def,cellHessianPoly_eval]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [hD t ht]

theorem cellGroupedTensorParts_eval {n : Nat} (V : Fin 120 → Fin 10 → IntVec)
    (c : Fin n → SecondaryCell) (D : Fin n → Poly)
    (groups : List (Fin n × List (Fin n)))
    (hD : ∀ g∈groups,∀ t∈g.2,D t=D g.1)
    (w : Fin 10 → ℝ) (i j : Fin 4) :
    eval (extendWeight w)
      (sumFast (groups.map fun g => cellGroupedTensor V c D g.1 g.2 i j))=
      ((groups.map Prod.snd).flatten.map fun t => eval (extendWeight w) (D t)*
        cellHessian (secondaryVertex V w) (c t) i j).sum := by
  rw [eval_sumFast]
  induction groups with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,List.sum_cons,List.flatten_cons,List.map_append,List.sum_append]
    rw [cellGroupedTensor_eval V c D g.1 g.2 (hD g (List.mem_cons_self)) w i j]
    rw [ih (fun k hk => hD k (List.mem_cons_of_mem _ hk))]

theorem cellGroupedTensorFull_eval {n : Nat} (V : Fin 120 → Fin 10 → IntVec)
    (c : Fin n → SecondaryCell) (D : Fin n → Poly)
    (groups : List (Fin n × List (Fin n)))
    (hD : ∀ g∈groups,∀ t∈g.2,D t=D g.1)
    (hcover : (groups.map Prod.snd).flatten.Perm (List.ofFn (fun t : Fin n => t)))
    (w : Fin 10 → ℝ) (i j : Fin 4) :
    eval (extendWeight w)
      (sumFast (groups.map fun g => cellGroupedTensor V c D g.1 g.2 i j))=
      ∑ t,eval (extendWeight w) (D t)*cellHessian (secondaryVertex V w) (c t) i j := by
  rw [cellGroupedTensorParts_eval V c D groups hD w i j,
    (hcover.map (fun t => eval (extendWeight w) (D t)*
      cellHessian (secondaryVertex V w) (c t) i j)).sum_eq,
    List.map_ofFn,List.sum_ofFn]
  rfl

end D4.Secondary
