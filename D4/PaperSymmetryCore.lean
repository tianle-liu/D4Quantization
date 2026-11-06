import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

/-! Actual generated permutation subgroups and explicit finite enumerations. -/
namespace D4.PaperSymmetry
abbrev Perm := Equiv.Perm (Fin 10)

def word (a b : Perm) : List Bool → Perm :=
  List.rec 1 (fun c _ p => (if c then b else a)*p)

theorem word_mem (a b : Perm) (w : List Bool) :
    word a b w ∈ Subgroup.closure ({a,b} : Set Perm) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons c w ih =>
    apply Subgroup.mul_mem _ _ ih
    cases c <;> exact Subgroup.subset_closure (by simp)

def tableSubgroup (ps : List Perm) (h1 : (1:Perm) ∈ ps)
    (hm : ∀ p ∈ ps, ∀ q ∈ ps, p*q ∈ ps)
    (hi : ∀ p ∈ ps, p⁻¹ ∈ ps) : Subgroup Perm where
  carrier := {p | p ∈ ps}
  one_mem' := h1
  mul_mem' := fun hp hq => hm _ hp _ hq
  inv_mem' := fun hp => hi _ hp

theorem tableSubgroup_eq_closure (ps : List Perm) (h1 : (1:Perm) ∈ ps)
    (hm : ∀ p ∈ ps, ∀ q ∈ ps, p*q ∈ ps) (hi : ∀ p ∈ ps, p⁻¹ ∈ ps)
    (a b : Perm) (hab : a ∈ ps ∧ b ∈ ps) (ws : List (List Bool))
    (hw : ws.map (word a b) = ps) :
    tableSubgroup ps h1 hm hi = Subgroup.closure ({a,b} : Set Perm) := by
  apply le_antisymm
  · intro p hp
    change p ∈ ps at hp
    rw [← hw] at hp
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hp
    exact word_mem a b w
  · exact (Subgroup.closure_le (tableSubgroup ps h1 hm hi)).mpr (by
      intro p hp
      rcases Set.mem_insert_iff.mp hp with rfl | hp
      · exact hab.1
      · have he : p=b := hp
        subst p
        exact hab.2)

theorem tableSubgroup_card (ps : List Perm) (h1 : (1:Perm) ∈ ps)
    (hm : ∀ p ∈ ps, ∀ q ∈ ps, p*q ∈ ps) (hi : ∀ p ∈ ps, p⁻¹ ∈ ps) :
    Nat.card (tableSubgroup ps h1 hm hi) = ps.toFinset.card := by
  classical
  letI : Fintype (tableSubgroup ps h1 hm hi) :=
    Fintype.ofFinset ps.toFinset (fun p => by simp [tableSubgroup])
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_ofFinset ps.toFinset (fun p => by simp [tableSubgroup])

end D4.PaperSymmetry
