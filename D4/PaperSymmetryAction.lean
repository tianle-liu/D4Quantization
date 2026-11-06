import D4.PaperSymmetryCore
import D4.Certificate
import Mathlib.Tactic.IntervalCases

/-! Polynomial invariance is propagated through the actual generated subgroup. -/
noncomputable section
namespace D4.PaperSymmetry
open Certificate

def extend (p : Perm) (n : Nat) : Nat := if h : n<10 then (p ⟨n,h⟩).val else n

def encoding (p : Perm) : List Nat := List.ofFn fun i : Fin 10 => (p i).val

theorem extend_mul (p q : Perm) (n : Nat) : extend (p*q) n=extend p (extend q n) := by
  by_cases h : n<10
  · simp [extend,h,(q ⟨n,h⟩).isLt,Equiv.Perm.mul_apply]
  · simp [extend,h]

theorem extend_one (n : Nat) : extend 1 n=n := by
  by_cases h : n<10 <;> simp [extend,h]

theorem extend_inv (p : Perm) (n : Nat) : extend p⁻¹ (extend p n)=n := by
  rw [← extend_mul,inv_mul_cancel,extend_one]

def invariantGroup (f : (Nat → ℝ) → ℝ) : Subgroup Perm where
  carrier := {p | ∀ x, f (fun n => x (extend p n))=f x}
  one_mem' := by intro x; simp only [extend_one]
  mul_mem' := by
    intro p q hp hq x
    simp only [extend_mul]
    exact (hq (fun n => x (extend p n))).trans (hp x)
  inv_mem' := by
    intro p hp x
    have h := hp (fun n => x (extend p⁻¹ n))
    simpa only [extend_inv] using h.symm

theorem invariant_generated (f : (Nat → ℝ) → ℝ) (a b : Perm)
    (ha : ∀ x, f (fun n => x (extend a n))=f x)
    (hb : ∀ x, f (fun n => x (extend b n))=f x)
    {p : Perm} (hp : p ∈ Subgroup.closure ({a,b}:Set Perm)) :
    ∀ x, f (fun n => x (extend p n))=f x := by
  apply (Subgroup.closure_le (invariantGroup f)).mpr ?_ hp
  intro q hq
  rcases Set.mem_insert_iff.mp hq with rfl | hq
  · exact ha
  · have he : q=b := hq
    subst q
    exact hb

theorem eval_agrees (p : Poly) (x y : Nat → ℝ)
    (h : ∀ t ∈ p, ∀ i ∈ t.1, x i=y i) : eval x p=eval y p := by
  unfold eval
  congr 1
  apply List.map_congr_left
  intro t ht
  congr 1
  unfold monomial
  congr 1
  exact List.map_congr_left fun i hi => h t ht i hi

theorem eval_rename_encoding (p : Poly) (g : Perm) (x : Nat → ℝ)
    (hp : ∀ t ∈ p, ∀ i ∈ t.1, i<10) :
    eval x (rename (encoding g) p)=eval (fun n => x (extend g n)) p := by
  rw [eval_rename]
  apply eval_agrees
  intro t ht i hi
  have h := hp t ht i hi
  congr 1
  interval_cases i <;> rfl

theorem invariant_of_rename (p : Poly) (g : Perm)
    (hp : ∀ t ∈ p, ∀ i ∈ t.1, i<10)
    (he : rename (encoding g) p=p) :
    ∀ x, eval (fun n => x (extend g n)) p=eval x p := by
  intro x
  rw [← eval_rename_encoding p g x hp,he]

end D4.PaperSymmetry
