import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Ring
import D4.Schur
import D4.CertificateSort

/-!
A small exact sparse-polynomial certificate checker. Its executable functions
are ordinary Lean definitions; their semantic soundness is proved below.
Generated equalities are checked by `decide`, using kernel reduction only.
Coefficients are integers and a monomial is the sorted list of its variables.
-/
namespace D4.Certificate

abbrev Monomial := List Nat
abbrev Poly := List (Monomial × Int)

def monomial (x : Nat → ℝ) (m : Monomial) : ℝ := (m.map x).prod
def eval (x : Nat → ℝ) (p : Poly) : ℝ :=
  (p.map fun t => (t.2 : ℝ) * monomial x t.1).sum

def key (m : Monomial) : Nat := m.foldl (fun k i => k * 11 + i + 1) 0

-- Use the primitive recursor explicitly: equation-compiler recursion produces
-- `List.brecOn`, which is expensive on the large certificate lists in the kernel.
def collect : Poly → Poly :=
  List.rec [] (fun t _ rest => match rest with
    | [] => [t]
    | u :: us => if t.1 = u.1 then (t.1, t.2 + u.2) :: us else t :: u :: us)

def normalize (p : Poly) : Poly :=
  (collect (D4.CertificateSort.sort (fun s t => key s.1 ≤ key t.1) p)).filter fun t => t.2 != 0

def normalizeRuns (ps : List Poly) : Poly :=
  (collect (D4.CertificateSort.sortFuel (fun s t => key s.1 ≤ key t.1) 32 ps)).filter fun t => t.2 != 0

def add (p q : Poly) : Poly := normalize (p ++ q)
def scale (c : Int) (p : Poly) : Poly := p.map fun t => (t.1, c * t.2)
def mul (p q : Poly) : Poly := normalizeRuns <| q.map fun s =>
  p.map fun t => ((s.1 ++ t.1).insertionSort (· ≤ ·), s.2 * t.2)
def power (p : Poly) : Nat → Poly
  | 0 => [([], 1)]
  | n + 1 => mul (power p n) p
def sum (ps : List Poly) : Poly := normalize ps.flatten
def rename (g : List Nat) (p : Poly) : Poly := normalize <| p.map fun t =>
  ((t.1.map fun i => g[i]!).insertionSort (· ≤ ·), t.2)
def nonnegative (p : Poly) : Bool := p.all fun t => decide (0 ≤ t.2)

@[simp] theorem eval_nil (x : Nat → ℝ) : eval x [] = 0 := rfl
@[simp] theorem eval_cons (x : Nat → ℝ) (t : Monomial × Int) (ts : Poly) :
    eval x (t :: ts) = (t.2 : ℝ) * monomial x t.1 + eval x ts := rfl
@[simp] theorem eval_append (x : Nat → ℝ) (p q : Poly) :
    eval x (p ++ q) = eval x p + eval x q := by simp [eval]

theorem eval_perm (x : Nat → ℝ) {p q : Poly} (h : p.Perm q) :
    eval x p = eval x q := (h.map _).sum_eq

theorem eval_collect (x : Nat → ℝ) (p : Poly) : eval x (collect p) = eval x p := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
    simp only [collect]
    split <;> rename_i h <;> change collect ts = _ at h
    · simp only [eval_cons, eval_nil]
      rw [← ih, h, eval_nil]
    · rename_i u us
      split_ifs with he
      · simp only [eval_cons, Int.cast_add]
        rw [← ih, h, eval_cons, ← he]
        ring
      · simp only [eval_cons]
        rw [← ih, h, eval_cons]

theorem eval_filter (x : Nat → ℝ) (p : Poly) :
    eval x (p.filter fun t => t.2 != 0) = eval x p := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
    by_cases h : t.2 = 0
    · simp [h, ih]
    · simp [h, ih]

@[simp] theorem eval_normalize (x : Nat → ℝ) (p : Poly) :
    eval x (normalize p) = eval x p := by
  rw [normalize, eval_filter, eval_collect]
  exact eval_perm x (D4.CertificateSort.sort_perm _ _)

@[simp] theorem eval_normalizeRuns (x : Nat → ℝ) (ps : List Poly) :
    eval x (normalizeRuns ps) = eval x ps.flatten := by
  rw [normalizeRuns, eval_filter, eval_collect]
  exact eval_perm x (D4.CertificateSort.sortFuel_perm _ _ _)

@[simp] theorem eval_add (x : Nat → ℝ) (p q : Poly) :
    eval x (add p q) = eval x p + eval x q := by simp [add]

@[simp] theorem eval_scale (x : Nat → ℝ) (c : Int) (p : Poly) :
    eval x (scale c p) = (c : ℝ) * eval x p := by
  induction p with
  | nil => simp [scale]
  | cons t ts ih =>
    change (↑(c * t.2) : ℝ) * monomial x t.1 + eval x (scale c ts) = _
    simp [ih, mul_add, mul_assoc]

@[simp] theorem monomial_append (x : Nat → ℝ) (m n : Monomial) :
    monomial x (m ++ n) = monomial x m * monomial x n := by simp [monomial]

@[simp] theorem monomial_sort (x : Nat → ℝ) (m : Monomial) :
    monomial x (m.insertionSort (· ≤ ·)) = monomial x m :=
  ((List.perm_insertionSort _ _).map _).prod_eq

theorem eval_mul_row (x : Nat → ℝ) (s : Monomial × Int) (q : Poly) :
    eval x (q.map fun t => ((s.1 ++ t.1).insertionSort (· ≤ ·), s.2 * t.2)) =
    ((s.2 : ℝ) * monomial x s.1) * eval x q := by
  induction q with
  | nil => simp
  | cons t ts ih => simp [ih, mul_add]; ring

@[simp] theorem eval_mul (x : Nat → ℝ) (p q : Poly) :
    eval x (mul p q) = eval x p * eval x q := by
  unfold mul
  rw [eval_normalizeRuns]
  induction q with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.flatten_cons, eval_append, eval_mul_row, ih, eval_cons]
    ring

@[simp] theorem eval_power (x : Nat → ℝ) (p : Poly) (n : Nat) :
    eval x (power p n) = eval x p ^ n := by
  induction n with
  | zero => simp [power, monomial]
  | succ n ih => simp [power, ih, pow_succ]

@[simp] theorem eval_sum (x : Nat → ℝ) (ps : List Poly) :
    eval x (sum ps) = (ps.map (eval x)).sum := by
  unfold sum
  rw [eval_normalize]
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

@[simp] theorem eval_rename (x : Nat → ℝ) (g : List Nat) (p : Poly) :
    eval x (rename g p) = eval (fun i => x g[i]!) p := by
  unfold rename
  rw [eval_normalize]
  induction p with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, eval_cons, monomial_sort, ih]
    congr 2
    simp only [monomial, List.map_map, Function.comp_def]

theorem monomial_nonneg (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) (m : Monomial) :
    0 ≤ monomial x m := by
  induction m with
  | nil => simp [monomial]
  | cons i m ih => exact mul_nonneg (hx i) ih

theorem eval_nonneg (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (p : Poly) (hp : nonnegative p = true) : 0 ≤ eval x p := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
  apply mul_nonneg
  · exact_mod_cast (of_decide_eq_true (List.all_eq_true.mp hp t ht) : (0 : Int) ≤ t.2)
  · exact monomial_nonneg x hx t.1

inductive Factor where
  | square (p : Poly)
  | schur (u v w : Nat)
  deriving DecidableEq, Repr

def schurPoly (u v w : Nat) : Poly :=
  [([u,u,u],1), ([v,v,v],1), ([w,w,w],1), ([u,v,w],3),
   ([u,u,v],-1), ([u,u,w],-1), ([v,v,u],-1), ([v,v,w],-1),
   ([w,w,u],-1), ([w,w,v],-1)].map fun t => (t.1.insertionSort (· ≤ ·), t.2)

def Factor.expand : Factor → Poly
  | .square p => mul p p
  | .schur u v w => schurPoly u v w

theorem factor_nonneg (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) (f : Factor) :
    0 ≤ eval x f.expand := by
  cases f with
  | square p => simpa [Factor.expand, ← pow_two] using sq_nonneg (eval x p)
  | schur u v w =>
    have hs := D4.schur_nonneg (x u) (x v) (x w) (hx u) (hx v) (hx w)
    have he : eval x (schurPoly u v w) =
        x u^3 + x v^3 + x w^3 + 3*x u*x v*x w -
        x u^2*x v - x u^2*x w - x v^2*x u - x v^2*x w -
        x w^2*x u - x w^2*x v := by
      simp only [schurPoly, List.map_cons, List.map_nil, eval_cons,
        eval_nil, monomial_sort]
      simp only [monomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
      norm_num
      ring
    simpa [Factor.expand, he] using hs

structure Row where
  weight : Poly
  factor : Factor
  deriving DecidableEq, Repr

def Row.expand (r : Row) : Poly := mul r.weight r.factor.expand
def rowsNonnegative (rs : List Row) : Bool := rs.all fun r => nonnegative r.weight

theorem rows_nonneg (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (rs : List Row) (hr : rowsNonnegative rs = true) :
    0 ≤ eval x (sum (rs.map Row.expand)) := by
  rw [eval_sum]
  apply List.sum_nonneg
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  obtain ⟨r, hrmem, rfl⟩ := List.mem_map.mp hp
  rw [Row.expand, eval_mul]
  exact mul_nonneg (eval_nonneg x hx r.weight (List.all_eq_true.mp hr r hrmem))
    (factor_nonneg x hx r.factor)

theorem symmetry_sum_nonneg (p : Poly) (groups : List (List Nat))
    (hp : ∀ (x : Nat → ℝ), (∀ i, 0 ≤ x i) → 0 ≤ eval x p)
    (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ eval x (sum (groups.map fun g => rename g p)) := by
  rw [eval_sum]
  apply List.sum_nonneg
  intro a ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hq
  rw [eval_rename]
  exact hp _ (fun i => hx _)

theorem certificate_nonneg (target unsym sym remainder : Poly)
    (rows : List Row) (groups : List (List Nat)) (s d : Int)
    (hs : 0 < s) (hd : 0 ≤ d)
    (hrows : rowsNonnegative rows = true)
    (hunsym : sum (rows.map Row.expand) = unsym)
    (hsym : sum (groups.map fun g => rename g unsym) = sym)
    (hid : add (scale s target) (scale (-d) sym) = remainder)
    (hrem : nonnegative remainder = true)
    (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x target := by
  have hu (y : Nat → ℝ) (hy : ∀ i, 0 ≤ y i) : 0 ≤ eval y unsym := by
    rw [← hunsym]
    exact rows_nonneg y hy rows hrows
  have hsy : 0 ≤ eval x sym := by
    rw [← hsym]
    exact symmetry_sum_nonneg unsym groups hu x hx
  have hr := eval_nonneg x hx remainder hrem
  have he := congrArg (eval x) hid
  simp only [eval_add, eval_scale, Int.cast_neg] at he
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
  have hmul : 0 ≤ (s : ℝ) * eval x target := by
    have := mul_nonneg hd' hsy
    linarith
  exact nonneg_of_mul_nonneg_right hmul hs'

end D4.Certificate
