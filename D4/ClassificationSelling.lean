import D4.ClassificationDefs
import D4.KernelCompute

/-! A finite, kernel-checked set of unimodular Selling moves in dimension four.
Their energy differences imply the pair inequalities used in the covering proof. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D4.Classification
open Matrix Analytic

/-- Flip vertex `i`, leave `j,k` fixed, and add vertex `i` to the remaining
 two superbase vectors. The dependent vertex is omitted from the matrix. -/
def sellingMatrix (i j k : Fin 5) : IntegerMatrix := fun r c =>
  let l : Fin 5 := c.succ
  if l = i then -(superVector i r)
  else if l = j ∨ l = k then superVector l r
  else superVector l r + superVector i r

/-- All sixty admissible moves are genuinely unimodular. -/
theorem selling_det : ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
    (sellingMatrix i j k).det = -1 := by decide +kernel

noncomputable section

theorem selling_energy (Q : RealGram) (hQ : Q.IsSymm)
    (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    energy (transform Q (sellingMatrix i j k)) =
      energy Q - 2 * (superInner Q i j + superInner Q i k) := by
  have h10 := hQ.apply 0 1
  have h20 := hQ.apply 0 2
  have h30 := hQ.apply 0 3
  have h21 := hQ.apply 1 2
  have h31 := hQ.apply 1 3
  have h32 := hQ.apply 2 3
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
  all_goals
    unfold energy transform
    simp_rw [quadratic_congruence]
    norm_num [superInner, sellingMatrix, superVector,
      realMatrix, quadratic, castVec, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Fin.succ, h10, h20, h30, h21, h31, h32]
    <;> dsimp [Fin.instOfNat, Fin.ofNat', Fin.lt_def, Fin.castSucc,
      Fin.succ, Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
    <;> norm_num [Fin.mk.injEq, h10, h20, h30, h21, h31, h32]
    <;> ring

/-- Energy minimization forces the inequalities; none are assumed. -/
theorem pairReduced_of_energyMinimal {Q : RealGram} (hQ : Q.IsSymm)
    (hmin : EnergyMinimal Q) : PairReduced Q := by
  intro i j k hij hik hjk
  have hu : IsUnit (sellingMatrix i j k).det := by
    rw [selling_det i j k hij hik hjk]
    exact isUnit_neg_one
  have h := hmin (sellingMatrix i j k) hu
  rw [selling_energy Q hQ i j k hij hik hjk] at h
  linarith

end
end D4.Classification
