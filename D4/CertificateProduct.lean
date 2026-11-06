import D4.CertificateFast

/-! Sparse products collect equal monomials during every merge pass.
The semantic theorem holds for arbitrary input lists. -/
namespace D4.Certificate

def mulMerge (p q : Poly) : Poly :=
  sumFast (q.map fun s => p.map fun t =>
    ((s.1 ++ t.1).insertionSort (· ≤ ·),s.2 * t.2))

@[simp] theorem eval_mulMerge (x : Nat → ℝ) (p q : Poly) :
    eval x (mulMerge p q) = eval x p * eval x q := by
  rw [mulMerge,eval_sumFast]
  induction q with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons,List.sum_cons,eval_mul_row,eval_cons]
    rw [ih]
    ring

end D4.Certificate
