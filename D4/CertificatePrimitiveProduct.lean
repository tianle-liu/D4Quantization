import D4.CertificateProduct

/-! The same checked sparse product, with a primitive list recursion for
both maps. This changes computation only; the existing product theorem
establishes its mathematical interpretation. -/
namespace D4.Certificate

def mapRec {α β : Type*} (f : α → β) (xs : List α) : List β :=
  List.rec [] (fun a _ rest => f a :: rest) xs

theorem mapRec_eq_map {α β : Type*} (f : α → β) (xs : List α) :
    mapRec f xs = xs.map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [mapRec, List.rec, List.map_cons] at *; exact congrArg (List.cons (f a)) ih

def mulMergePrim (p q : Poly) : Poly :=
  sumFast (mapRec (fun s => mapRec (fun t =>
    ((s.1 ++ t.1).insertionSort (· ≤ ·), s.2 * t.2)) p) q)

theorem mulMergePrim_eq_mulMerge (p q : Poly) :
    mulMergePrim p q = mulMerge p q := by
  simp only [mulMergePrim, mulMerge, mapRec_eq_map]

@[simp] theorem eval_mulMergePrim (x : Nat → ℝ) (p q : Poly) :
    eval x (mulMergePrim p q) = eval x p * eval x q := by
  rw [mulMergePrim_eq_mulMerge, eval_mulMerge]

end D4.Certificate
