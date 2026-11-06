import D4.PaperSymmetryCore
import Mathlib.Data.Finset.Image
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The first symmetry group is the actual action of S5 on the ten edges of K5. -/
set_option maxRecDepth 10000
namespace D4.PaperSymmetry.C1
open D4.PaperSymmetry

def lo : Fin 10 → Fin 5 := ![0,0,0,0,1,1,1,2,2,3]
def hi : Fin 10 → Fin 5 := ![1,2,3,4,2,3,4,3,4,4]
def edge (e : Fin 10) : Finset (Fin 5) := {lo e,hi e}

theorem lo_ne_hi (e : Fin 10) : lo e≠hi e := by fin_cases e <;> decide

theorem edge_injective : Function.Injective edge := by decide +kernel

def index (i j : Fin 5) : Fin 10 :=
  ⟨if min i.val j.val=0 then max i.val j.val-1 else
    if min i.val j.val=1 then max i.val j.val+2 else
    if min i.val j.val=2 then max i.val j.val+4 else 9,
    by fin_cases i <;> fin_cases j <;> decide⟩

theorem edge_index (i j : Fin 5) (h : i≠j) : edge (index i j)={i,j} := by
  fin_cases i <;> fin_cases j <;> first | exact False.elim (h rfl) | decide +kernel

def action (p : Equiv.Perm (Fin 5)) (e : Fin 10) : Fin 10 := index (p (lo e)) (p (hi e))

theorem edge_action (p : Equiv.Perm (Fin 5)) (e : Fin 10) :
    edge (action p e)=(edge e).image p := by
  rw [action,edge_index _ _ (p.injective.ne (lo_ne_hi e))]
  simp [edge]

theorem action_one (e : Fin 10) : action 1 e=e := by
  apply edge_injective
  rw [edge_action]
  simp

theorem action_mul (p q : Equiv.Perm (Fin 5)) (e : Fin 10) :
    action (p*q) e=action p (action q e) := by
  apply edge_injective
  simp only [edge_action,Finset.image_image,Equiv.Perm.coe_mul,Function.comp_def]

def edgePerm (p : Equiv.Perm (Fin 5)) : Perm where
  toFun := action p
  invFun := action p⁻¹
  left_inv e := by rw [← action_mul,inv_mul_cancel,action_one]
  right_inv e := by rw [← action_mul,mul_inv_cancel,action_one]

def edgeHom : Equiv.Perm (Fin 5) →* Perm where
  toFun := edgePerm
  map_one' := by apply Equiv.ext; intro e; exact action_one e
  map_mul' p q := by apply Equiv.ext; intro e; exact action_mul p q e

theorem edgeHom_injective : Function.Injective edgeHom := by
  intro p q hpq
  have hpairs (i j : Fin 5) (hij : i≠j) : ({p i,p j}:Finset (Fin 5))={q i,q j} := by
    have h := congrArg (fun g : Perm => edge (g (index i j))) hpq
    change edge (action p (index i j))=edge (action q (index i j)) at h
    simpa only [edge_action,edge_index i j hij,Finset.image_insert,Finset.image_singleton] using h
  apply Equiv.ext
  intro i
  have hjk : ∃ j k : Fin 5, i≠j ∧ i≠k ∧ j≠k := by fin_cases i <;> decide
  obtain ⟨j,k,hij,hik,hjk⟩ := hjk
  have h1 : p i=q i ∨ p i=q j := by
    have h : p i ∈ ({q i,q j}:Finset (Fin 5)) := by rw [← hpairs i j hij]; simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using h
  have h2 : p i=q i ∨ p i=q k := by
    have h : p i ∈ ({q i,q k}:Finset (Fin 5)) := by rw [← hpairs i k hik]; simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using h
  rcases h1 with h | h
  · exact h
  rcases h2 with h' | h'
  · exact h'
  exact False.elim (hjk (q.injective (h.symm.trans h')))

def subgroup : Subgroup Perm := edgeHom.range

theorem order : Nat.card subgroup=120 := by
  have hcard : Nat.card (Equiv.Perm (Fin 5))=120 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  exact (Nat.card_congr (Equiv.ofInjective edgeHom edgeHom_injective)).symm.trans hcard

end D4.PaperSymmetry.C1
