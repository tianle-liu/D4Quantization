import D4.ClassificationMinimum
import D4.ClassificationSelling
import D4.ClassificationPatterns

/-!
# Unconditional coverage by the three displayed four-dimensional cones

The proof minimizes the sum of five quadratic values over actual unimodular
integer bases. The sixty elementary Selling moves force pair reduction;
permuting the superbase and explicit nonnegative matrix decompositions then
place the form in one of the three cones. No external classification theorem
or project-specific axiom is used.
-/

namespace D4
open Classification

/-- Every positive-definite real four-dimensional Gram matrix is integrally
congruent to a nonnegative combination in one of the article's three cones. -/
theorem secondaryConeCoverage : SecondaryConeCoverageTarget := by
  intro Q hQ
  obtain ⟨R, hQR, hR, hmin⟩ := exists_energyMinimal hQ
  have hred : PairReduced R :=
    pairReduced_of_energyMinimal (isSymm_of_posDef hR) hmin
  obtain ⟨S, hRS, hS⟩ := coverage_of_pairReduced hR hred
  exact ⟨S, hQR.trans hRS, hS⟩

end D4
