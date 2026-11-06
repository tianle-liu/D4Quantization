import D4.PaperMonomials
import D4.PaperSymmetryAction
import Mathlib.GroupTheory.GroupAction.Quotient

/-! The actual permutation action on all homogeneous degree-five monomials. -/
namespace D4.PaperSymmetry
open Certificate PaperStatistics
attribute [local irreducible] degreeFive
set_option maxHeartbeats 10000


def monomialAction (p : Perm) (m : Monomial) : Monomial :=
  (m.map (extend p)).insertionSort (· ≤ ·)

theorem monomialAction_mem (p : Perm) {m : Monomial} (hm : m ∈ degreeFive) :
    monomialAction p m ∈ degreeFive := by
  obtain ⟨hlen,hs,hb⟩ := (degreeFive_complete m).mp hm
  apply (degreeFive_complete _).mpr
  refine ⟨?_,List.sorted_insertionSort _ _,?_⟩
  · simp only [monomialAction,List.length_insertionSort,List.length_map,hlen]
  · intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ((List.mem_insertionSort (· ≤ ·)).mp hi)
    have h := hb j hj
    simp only [extend,dif_pos h]
    exact (p ⟨j,h⟩).isLt

theorem monomialAction_mul (p q : Perm) (m : Monomial) :
    monomialAction p (monomialAction q m)=monomialAction (p*q) m := by
  apply List.eq_of_perm_of_sorted _ (List.sorted_insertionSort _ _) (List.sorted_insertionSort _ _)
  have h := (List.perm_insertionSort (· ≤ ·) (m.map (extend q))).map (extend p)
  have he : (m.map (extend q)).map (extend p)=m.map (extend (p*q)) := by
    rw [List.map_map]
    congr 1
    funext i
    exact (extend_mul p q i).symm
  exact (List.perm_insertionSort _ _).trans (h.trans (he ▸ (List.perm_insertionSort _ _).symm))

theorem monomialAction_one {m : Monomial} (hm : m ∈ degreeFive) : monomialAction 1 m=m := by
  apply List.eq_of_perm_of_sorted _ (List.sorted_insertionSort _ _) ((degreeFive_complete m).mp hm).2.1
  have he : extend (1:Perm)=id := funext extend_one
  simpa only [he,List.map_id] using (List.perm_insertionSort (· ≤ ·) (m.map (extend 1)))

abbrev DegreeFiveMonomial := {m : Monomial // m ∈ degreeFive}

instance : Fintype DegreeFiveMonomial :=
  Fintype.ofFinset degreeFive.toFinset (fun m => List.mem_toFinset)

instance : MulAction Perm DegreeFiveMonomial where
  smul p m := ⟨monomialAction p m.1,monomialAction_mem p m.2⟩
  one_smul m := Subtype.ext (monomialAction_one m.2)
  mul_smul p q m := Subtype.ext (monomialAction_mul p q m.1).symm

def fixedCount (p : Perm) : Nat :=
  (degreeFive.filter (fun m => decide (monomialAction p m=m))).length

theorem card_list_filter {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup)
    (P : α → Prop) [DecidablePred P] :
    Nat.card {a : α // a ∈ l ∧ P a} = (l.filter (fun a => decide (P a))).length := by
  classical
  let s := (l.filter (fun a => decide (P a))).toFinset
  have hs (a : α) : a ∈ s ↔ a ∈ l ∧ P a := by
    simp only [s,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
  let e : {a // a ∈ l ∧ P a} ≃ s :=
    { toFun := fun a => ⟨a.1,(hs a.1).mpr a.2⟩
      invFun := fun a => ⟨a.1,(hs a.1).mp a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_finsetCard]
  exact List.toFinset_card_of_nodup (hl.filter _)

theorem fixedCount_eq (p : Perm) :
    fixedCount p=Nat.card (MulAction.fixedBy DegreeFiveMonomial p) := by
  let e : MulAction.fixedBy DegreeFiveMonomial p ≃
      {m : Monomial // m ∈ degreeFive ∧ monomialAction p m=m} :=
    { toFun := fun m => ⟨m.1.1,⟨m.1.2,congrArg Subtype.val m.2⟩⟩
      invFun := fun m => ⟨⟨m.1,m.2.1⟩,Subtype.ext m.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,card_list_filter degreeFive degreeFive_nodup]
  rfl

end D4.PaperSymmetry
