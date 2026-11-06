import D4.Certificate

/-!
# Merge-based exact polynomial checker

The merge is linear for already sorted sparse inputs. Its semantic theorem
holds for arbitrary input lists, so sorting conventions affect efficiency
and canonical form only, never soundness.
-/
namespace D4.Certificate

/-- Structurally recursive inner merge. The continuation handles the tail of
the first input, avoiding well-founded recursion during kernel reduction. -/
def mergeHead (a : Monomial × Int) (ps : Poly) (next : Poly → Poly) : Poly → Poly :=
  List.rec (a :: ps) (fun b qs rest =>
    if a.1 = b.1 then
      if a.2 + b.2 = 0 then next qs
      else (a.1, a.2 + b.2) :: next qs
    else if key a.1 ≤ key b.1 then a :: next (b :: qs)
    else b :: rest)

/-- Add two sorted sparse polynomials, collecting matching monomials.
The equality test is on monomials themselves, not merely on their sort keys.
Both recursions are structural, so kernel reduction needs no accessibility proof. -/
def mergeAdd : Poly → Poly → Poly :=
  List.rec (fun q => q) (fun a ps next q => mergeHead a ps next q)

private theorem eval_mergeHead (x : Nat → ℝ) (a : Monomial × Int) (ps : Poly)
    (next : Poly → Poly) (hnext : ∀ q, eval x (next q) = eval x ps + eval x q)
    (q : Poly) : eval x (mergeHead a ps next q) = eval x (a :: ps) + eval x q := by
  induction q with
  | nil => simp [mergeHead]
  | cons b qs ih =>
    simp only [mergeHead] at ih ⊢
    by_cases he : a.1 = b.1
    · by_cases hz : a.2 + b.2 = 0
      · rw [if_pos he, if_pos hz, hnext]
        have hz' : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
        have hc := congrArg (fun c : ℝ => c * monomial x b.1) hz'
        dsimp at hc
        simp only [eval_cons, he]
        nlinarith only [hc]
      · rw [if_pos he, if_neg hz]
        simp only [eval_cons, Int.cast_add, hnext, he]
        ring
    · by_cases hle : key a.1 ≤ key b.1
      · rw [if_neg he, if_pos hle]
        simp only [eval_cons, hnext]
        ring
      · rw [if_neg he, if_neg hle]
        simp only [eval_cons, ih]
        ring

/-- The faster addition preserves the interpretation of every polynomial. -/
@[simp] theorem eval_mergeAdd (x : Nat → ℝ) (p q : Poly) :
    eval x (mergeAdd p q) = eval x p + eval x q := by
  induction p generalizing q with
  | nil => simp [mergeAdd]
  | cons a ps ih => exact eval_mergeHead x a ps (mergeAdd ps) ih q

def mergePairsAux : List Poly → Option Poly → List Poly :=
  List.rec (fun pending => pending.toList) (fun b _ next pending =>
    match pending with
    | none => next (some b)
    | some a => mergeAdd a b :: next none)

/-- One balanced merging pass, with primitive list recursion. -/
def mergePairs (ps : List Poly) : List Poly := mergePairsAux ps none

theorem eval_mergePairsAux (x : Nat → ℝ) (ps : List Poly) (pending : Option Poly) :
    ((mergePairsAux ps pending).map (eval x)).sum =
      (pending.toList.map (eval x)).sum + (ps.map (eval x)).sum := by
  induction ps generalizing pending with
  | nil => cases pending <;> simp [mergePairsAux]
  | cons b bs ih =>
    cases pending with
    | none => simpa [mergePairsAux] using ih (some b)
    | some a => simpa [mergePairsAux, add_assoc] using
        congrArg (fun z => eval x (mergeAdd a b) + z) (ih none)

theorem eval_mergePairs (x : Nat → ℝ) (ps : List Poly) :
    ((mergePairs ps).map (eval x)).sum = (ps.map (eval x)).sum := by
  simpa [mergePairs] using eval_mergePairsAux x ps none

def sumFuel : Nat → List Poly → Poly :=
  Nat.rec List.flatten (fun _ next ps =>
    match ps with
    | [] => []
    | [p] => p
    | _ => next (mergePairs ps))

theorem eval_sumFuel (x : Nat → ℝ) (fuel : Nat) (ps : List Poly) :
    eval x (sumFuel fuel ps) = (ps.map (eval x)).sum := by
  induction fuel generalizing ps with
  | zero =>
    change eval x ps.flatten = (ps.map (eval x)).sum
    induction ps with
    | nil => rfl
    | cons p ps ih => simp [ih]
  | succ n ih =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      cases ps with
      | nil => simp [sumFuel]
      | cons q ps =>
        change eval x (sumFuel n (mergePairs (p :: q :: ps))) = _
        rw [ih, eval_mergePairs]

/-- Merge in balanced passes to bound kernel reduction stack depth. -/
def sumFast (ps : List Poly) : Poly := sumFuel 32 ps

@[simp] theorem eval_sumFast (x : Nat → ℝ) (ps : List Poly) :
    eval x (sumFast ps) = (ps.map (eval x)).sum := by
  exact eval_sumFuel x 32 ps

/-- Faster computation is extensionally equal to the original summation. -/
theorem eval_sumFast_eq_sum (x : Nat → ℝ) (ps : List Poly) :
    eval x (sumFast ps) = eval x (sum ps) := by simp

theorem substitution_sum_nonneg (p : Poly) (gs : List (List Nat))
    (hp : ∀ (x : Nat → ℝ), (∀ i, 0 ≤ x i) → 0 ≤ eval x p)
    (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ eval x (sumFast (gs.map fun g => rename g p)) := by
  rw [eval_sumFast_eq_sum]
  exact symmetry_sum_nonneg p gs hp x hx

theorem certificate_from_nonnegative_sym (target sym remainder : Poly) (s d : Int)
    (hs : 0 < s) (hd : 0 ≤ d)
    (hsym : ∀ (x : Nat → ℝ), (∀ i, 0 ≤ x i) → 0 ≤ eval x sym)
    (hid : mergeAdd (scale s target) (scale (-d) sym) = remainder)
    (hrem : nonnegative remainder = true)
    (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x target := by
  have hr := eval_nonneg x hx remainder hrem
  have he := congrArg (eval x) hid
  simp only [eval_mergeAdd, eval_scale, Int.cast_neg] at he
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
  have hmul : 0 ≤ (s : ℝ) * eval x target := by
    have := mul_nonneg hd' (hsym x hx)
    linarith
  exact nonneg_of_mul_nonneg_right hmul hs'

/-- A certificate theorem with the same semantic guarantees as the original
checker and merge-based computation for the large sums and final identity. -/
theorem certificate_nonneg_fast (target unsym sym remainder : Poly)
    (rows : List Row) (groups : List (List Nat)) (s d : Int)
    (hs : 0 < s) (hd : 0 ≤ d)
    (hrows : rowsNonnegative rows = true)
    (hunsym : sumFast (rows.map Row.expand) = unsym)
    (hsym : sumFast (groups.map fun g => rename g unsym) = sym)
    (hid : mergeAdd (scale s target) (scale (-d) sym) = remainder)
    (hrem : nonnegative remainder = true)
    (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x target := by
  have hu (y : Nat → ℝ) (hy : ∀ i, 0 ≤ y i) : 0 ≤ eval y unsym := by
    rw [← hunsym, eval_sumFast_eq_sum]
    exact rows_nonneg y hy rows hrows
  have hsy : 0 ≤ eval x sym := by
    rw [← hsym, eval_sumFast_eq_sum]
    exact symmetry_sum_nonneg unsym groups hu x hx
  have hr := eval_nonneg x hx remainder hrem
  have he := congrArg (eval x) hid
  simp only [eval_mergeAdd, eval_scale, Int.cast_neg] at he
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
  have hmul : 0 ≤ (s : ℝ) * eval x target := by
    have := mul_nonneg hd' hsy
    linarith
  exact nonneg_of_mul_nonneg_right hmul hs'

end D4.Certificate
