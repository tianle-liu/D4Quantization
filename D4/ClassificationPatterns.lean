import D4.ClassificationRelabel
import D4.ClassificationCones
import D4.KernelCompute

/-! Pair-reduced superbases have positive edges forming a matching. The
following explicit relabellings put that matching in the displayed cones. -/

namespace D4.Classification
open Matrix Analytic

/-- Send the labelled pair `(1,2)` to any two distinct vertices. -/
def sendPair (i j : Fin 5) : Equiv.Perm (Fin 5) :=
  (Equiv.swap (1 : Fin 5) i).trans
    (Equiv.swap ((Equiv.swap (1 : Fin 5) i) 2) j)

theorem sendPair_spec : ∀ i j : Fin 5, i ≠ j →
    sendPair i j 1 = i ∧ sendPair i j 2 = j := by decide +kernel

noncomputable section

theorem isSymm_of_posDef {Q : RealGram} (hQ : Q.PosDef) : Q.IsSymm := by
  simpa only [Matrix.IsHermitian, Matrix.IsSymm,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.1

/-- If both disjoint canonical edges are positive, order them and use C₃. -/
theorem coverage_of_two_positive {Q : RealGram} (hQ : Q.PosDef)
    (hred : PairReduced Q) (h12 : 0 < superInner Q 1 2)
    (h34 : 0 < superInner Q 3 4) :
    ∃ R, IntegralCongruent Q R ∧ InThreeCones R := by
  by_cases hab : superInner Q 3 4 ≤ superInner Q 1 2
  · exact ⟨Q, IntegralCongruent.refl Q,
      Or.inr (Or.inr (inSecondary3_of_pairReduced (isSymm_of_posDef hQ) hred h34.le hab))⟩
  · let σ : Equiv.Perm (Fin 5) := (Equiv.swap 1 3).trans (Equiv.swap 2 4)
    let R := transform Q (relabelMatrix σ)
    have hc : IntegralCongruent Q R := relabel_integralCongruent Q σ
    have hR : R.PosDef := hc.posDef hQ
    have hi12 : superInner R 1 2 = superInner Q 3 4 := by
      simp [R, superInner_relabel, σ, Equiv.trans_apply, Equiv.swap_apply_def]
    have hi34 : superInner R 3 4 = superInner Q 1 2 := by
      simp [R, superInner_relabel, σ, Equiv.trans_apply, Equiv.swap_apply_def]
    refine ⟨R, hc, Or.inr (Or.inr (inSecondary3_of_pairReduced
      (isSymm_of_posDef hR) (pairReduced_relabel hred σ) ?_ ?_))⟩
    · rw [hi34]; exact h12.le
    · rw [hi12, hi34]; exact (lt_of_not_ge hab).le

/-- Once one edge is fixed, only the three edges on the other vertices
need to be tested; the pair inequalities handle every incident edge. -/
theorem coverage_of_positive12 {Q : RealGram} (hQ : Q.PosDef)
    (hred : PairReduced Q) (h12 : 0 < superInner Q 1 2) :
    ∃ R, IntegralCongruent Q R ∧ InThreeCones R := by
  by_cases h03 : 0 < superInner Q 0 3
  · let σ : Equiv.Perm (Fin 5) := (Equiv.swap 0 4).trans (Equiv.swap 0 3)
    let R := transform Q (relabelMatrix σ)
    have hc : IntegralCongruent Q R := relabel_integralCongruent Q σ
    have hi12 : 0 < superInner R 1 2 := by
      simpa [R, superInner_relabel, σ, Equiv.trans_apply, Equiv.swap_apply_def] using h12
    have hi34 : 0 < superInner R 3 4 := by
      simpa [R, superInner_relabel, σ, Equiv.trans_apply, Equiv.swap_apply_def] using h03
    obtain ⟨S, hRS, hS⟩ := coverage_of_two_positive (hc.posDef hQ)
      (pairReduced_relabel hred σ) hi12 hi34
    exact ⟨S, hc.trans hRS, hS⟩
  by_cases h04 : 0 < superInner Q 0 4
  · let σ : Equiv.Perm (Fin 5) := Equiv.swap 0 3
    let R := transform Q (relabelMatrix σ)
    have hc : IntegralCongruent Q R := relabel_integralCongruent Q σ
    have hi12 : 0 < superInner R 1 2 := by
      simpa [R, superInner_relabel, σ, Equiv.swap_apply_def] using h12
    have hi34 : 0 < superInner R 3 4 := by
      simpa [R, superInner_relabel, σ, Equiv.swap_apply_def] using h04
    obtain ⟨S, hRS, hS⟩ := coverage_of_two_positive (hc.posDef hQ)
      (pairReduced_relabel hred σ) hi12 hi34
    exact ⟨S, hc.trans hRS, hS⟩
  by_cases h34 : 0 < superInner Q 3 4
  · exact coverage_of_two_positive hQ hred h12 h34
  exact ⟨Q, IntegralCongruent.refl Q,
    Or.inr (Or.inl (inSecondary2_of_pairReduced (isSymm_of_posDef hQ)
      hred h12.le (le_of_not_gt h03) (le_of_not_gt h04) (le_of_not_gt h34)))⟩

/-- The full linear classification of a pair-reduced positive-definite form. -/
theorem coverage_of_pairReduced {Q : RealGram} (hQ : Q.PosDef) (hred : PairReduced Q) :
    ∃ R, IntegralCongruent Q R ∧ InThreeCones R := by
  classical
  by_cases hp : ∃ i j : Fin 5, i ≠ j ∧ 0 < superInner Q i j
  · obtain ⟨i, j, hij, hpos⟩ := hp
    let σ := sendPair i j
    let R := transform Q (relabelMatrix σ)
    have hc : IntegralCongruent Q R := relabel_integralCongruent Q σ
    have hi12 : 0 < superInner R 1 2 := by
      obtain ⟨hs1, hs2⟩ := sendPair_spec i j hij
      simpa only [R, superInner_relabel, σ, hs1, hs2] using hpos
    obtain ⟨S, hRS, hS⟩ := coverage_of_positive12 (hc.posDef hQ)
      (pairReduced_relabel hred σ) hi12
    exact ⟨S, hc.trans hRS, hS⟩
  · refine ⟨Q, IntegralCongruent.refl Q,
      Or.inl (inPrincipalCone_of_superInner_nonpos (isSymm_of_posDef hQ) ?_)⟩
    intro i j hij
    exact le_of_not_gt (fun h => hp ⟨i,j,hij,h⟩)

end
end D4.Classification
