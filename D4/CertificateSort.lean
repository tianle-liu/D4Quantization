import Mathlib.Data.List.Sort

/-!
# Structurally recursive merge sort for kernel computation

Every executable recursion below is structural. Its permutation theorem is
all the polynomial checker needs: sorting is never trusted as a black box.
-/
namespace D4.CertificateSort
universe u
variable {α : Type u}

def mergeHead (r : α → α → Bool) (a : α) (as : List α)
    (next : List α → List α) : List α → List α :=
  List.rec (a :: as) (fun b bs rest =>
    if r a b then a :: next (b :: bs) else b :: rest)

def merge (r : α → α → Bool) : List α → List α → List α :=
  List.rec (fun bs => bs) (fun a as next bs => mergeHead r a as next bs)

private theorem mergeHead_perm (r : α → α → Bool) (a : α) (as : List α)
    (next : List α → List α) (hnext : ∀ bs, (next bs).Perm (as ++ bs))
    (bs : List α) : (mergeHead r a as next bs).Perm ((a :: as) ++ bs) := by
  induction bs with
  | nil => simp [mergeHead]
  | cons b bs ih =>
    by_cases h : r a b = true
    · simpa [mergeHead, h] using (hnext (b :: bs)).cons a
    · simp only [mergeHead, h, Bool.false_eq_true, ↓reduceIte]
      exact List.perm_cons_append_cons b ih

/-- The merge preserves all entries, for arbitrary input lists and comparator. -/
theorem merge_perm (r : α → α → Bool) (as bs : List α) :
    (merge r as bs).Perm (as ++ bs) := by
  induction as generalizing bs with
  | nil => simp [merge]
  | cons a as ih => exact mergeHead_perm r a as (merge r as) ih bs

/-- Pairing pass implemented with the primitive list recursor. -/
def mergePairsAux (r : α → α → Bool) : List (List α) → Option (List α) → List (List α) :=
  List.rec (fun pending => pending.toList) (fun b _ next pending =>
    match pending with
    | none => next (some b)
    | some a => merge r a b :: next none)

/-- One bottom-up merge pass. -/
def mergePairs (r : α → α → Bool) (runs : List (List α)) : List (List α) :=
  mergePairsAux r runs none

private theorem mergePairsAux_perm (r : α → α → Bool) (runs : List (List α))
    (pending : Option (List α)) :
    (mergePairsAux r runs pending).flatten.Perm (pending.toList.flatten ++ runs.flatten) := by
  induction runs generalizing pending with
  | nil => cases pending <;> simp [mergePairsAux]
  | cons b bs ih =>
    cases pending with
    | none => simpa [mergePairsAux] using ih (some b)
    | some a =>
      simpa only [mergePairsAux, List.flatten_cons, Option.toList_some,
        Option.toList_none, List.flatten_nil, List.append_nil, List.nil_append,
        List.append_assoc] using (merge_perm r a b).append (ih none)

theorem mergePairs_perm (r : α → α → Bool) (runs : List (List α)) :
    (mergePairs r runs).flatten.Perm runs.flatten := by
  simpa [mergePairs] using mergePairsAux_perm r runs none

/-- Fuel decreases structurally; singleton runs stop immediately. -/
def sortFuel (r : α → α → Bool) : Nat → List (List α) → List α :=
  Nat.rec List.flatten (fun _ next runs =>
    match runs with
    | [] => []
    | [as] => as
    | _ => next (mergePairs r runs))

theorem sortFuel_perm (r : α → α → Bool) (fuel : Nat) (runs : List (List α)) :
    (sortFuel r fuel runs).Perm runs.flatten := by
  induction fuel generalizing runs with
  | zero => rfl
  | succ n ih =>
    cases runs with
    | nil => rfl
    | cons as rest =>
      cases rest with
      | nil => simp [sortFuel]
      | cons bs rest =>
        exact (ih (mergePairs r (as :: bs :: rest))).trans (mergePairs_perm r _)

/-- Bottom-up merge sorting, implemented entirely with structural recursion. -/
def sort (r : α → α → Bool) (as : List α) : List α :=
  sortFuel r 32 (as.map fun a => [a])

theorem sort_perm (r : α → α → Bool) (as : List α) : (sort r as).Perm as := by
  have hs : (as.map fun a => [a]).flatten = as := by
    induction as with
    | nil => rfl
    | cons a as ih => simpa using congrArg (List.cons a) ih
  simpa only [sort, hs] using sortFuel_perm r 32 (as.map fun a => [a])

end D4.CertificateSort
