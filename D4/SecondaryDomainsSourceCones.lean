import D4.SecondaryDomainsClosed

/-! Identification of the classified closed cones with the exact three
 generator definitions used in the article's matrix and moment statements. -/
noncomputable section
namespace D4.Delaunay
open Analytic Matrix Set

theorem nonnegativeCone_iff_generated (i : Fin 3) (Q : SymGram) :
    Q ∈ nonnegativeCone i ↔ ∃ w : Fin 10 → ℝ, (∀ k, 0 ≤ w k) ∧ Q.1=coneForm i w := by
  constructor
  · intro h
    exact ⟨coneCoordinates i Q.1,h,(coneForm_coordinates i Q.1 Q.2).symm⟩
  · rintro ⟨w,hw,he⟩
    change ∀ k, 0 ≤ coneCoordinates i Q.1 k
    rw [he,coneCoordinates_form]
    exact hw

theorem nonnegativeCone_zero_iff (Q : SymGram) :
    Q ∈ nonnegativeCone 0 ↔ InPrincipalCone Q.1 := by
  exact nonnegativeCone_iff_generated 0 Q

theorem nonnegativeCone_one_iff (Q : SymGram) :
    Q ∈ nonnegativeCone 1 ↔ InSecondaryCone cone2Vectors Q.1 := by
  rw [nonnegativeCone_iff_generated]
  constructor
  · rintro ⟨w,hw,he⟩
    exact ⟨w 0,fun j => w j.succ,hw 0,fun j => hw j.succ,he⟩
  · rintro ⟨a,w,ha,hw,he⟩
    exact ⟨Fin.cons a w,fun k => Fin.cases ha hw k,he⟩

theorem nonnegativeCone_two_iff (Q : SymGram) :
    Q ∈ nonnegativeCone 2 ↔ InSecondaryCone cone3Vectors Q.1 := by
  rw [nonnegativeCone_iff_generated]
  constructor
  · rintro ⟨w,hw,he⟩
    exact ⟨w 0,fun j => w j.succ,hw 0,fun j => hw j.succ,he⟩
  · rintro ⟨a,w,ha,hw,he⟩
    exact ⟨Fin.cons a w,fun k => Fin.cases ha hw k,he⟩

theorem nonnegativeCone_exists_iff (Q : SymGram) :
    (∃ i : Fin 3, Q ∈ nonnegativeCone i) ↔ InThreeCones Q.1 := by
  constructor
  · rintro ⟨i,hi⟩
    fin_cases i
    · exact Or.inl ((nonnegativeCone_zero_iff Q).mp hi)
    · exact Or.inr (Or.inl ((nonnegativeCone_one_iff Q).mp hi))
    · exact Or.inr (Or.inr ((nonnegativeCone_two_iff Q).mp hi))
  · rintro (h | h | h)
    · exact ⟨0,(nonnegativeCone_zero_iff Q).mpr h⟩
    · exact ⟨1,(nonnegativeCone_one_iff Q).mpr h⟩
    · exact ⟨2,(nonnegativeCone_two_iff Q).mpr h⟩

end D4.Delaunay
