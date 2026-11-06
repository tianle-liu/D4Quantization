import D4.DelaunayData

namespace D4.Delaunay

set_option maxHeartbeats 0

set_option maxRecDepth 1000000

def singleLifting (j : Fin 10) : Fin 10 → ℤ := fun k => if k=j then 2 else 0

def doubleLifting (j : Fin 9) : Fin 10 → ℤ := singleLifting 0+singleLifting j.succ

def liftingCount (F : Fin 60 → FacetRecord) (v : Fin 10 → ℤ) : ℕ :=
  ((List.finRange 60).filter (fun i => decide ((F i).lifting=v))).length

theorem lifting1_classification : ∀ i, ∃ j, (facets1 i).lifting=singleLifting j := by decide +kernel

theorem lifting1_multiplicity : ∀ j, liftingCount facets1 (singleLifting j)=6 := by decide +kernel

theorem lifting2_classification : ∀ i, (facets2 i).lifting=singleLifting 0 ∨
    (∃ j : Fin 9, (facets2 i).lifting=singleLifting j.succ) ∨
    (∃ j : Fin 9, (facets2 i).lifting=doubleLifting j) := by decide +kernel

theorem lifting2_a_multiplicity : liftingCount facets2 (singleLifting 0)=6 := by decide +kernel

theorem lifting2_single_multiplicity : ∀ j : Fin 9, liftingCount facets2 (singleLifting j.succ)=4 := by decide +kernel

theorem lifting2_double_multiplicity : ∀ j : Fin 9, liftingCount facets2 (doubleLifting j)=2 := by decide +kernel

theorem lifting3_classification : ∀ i, (facets3 i).lifting=singleLifting 0 ∨
    (∃ j : Fin 9, (facets3 i).lifting=singleLifting j.succ) ∨
    (∃ j : Fin 9, (facets3 i).lifting=doubleLifting j) := by decide +kernel

theorem lifting3_a_multiplicity : liftingCount facets3 (singleLifting 0)=6 := by decide +kernel

theorem lifting3_single_multiplicity : ∀ j : Fin 9, liftingCount facets3 (singleLifting j.succ)=4 := by decide +kernel

theorem lifting3_double_multiplicity : ∀ j : Fin 9, liftingCount facets3 (doubleLifting j)=2 := by decide +kernel

end D4.Delaunay
