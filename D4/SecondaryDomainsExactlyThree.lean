import D4.SecondaryDomainsClassification
import D4.SecondaryTypeInvariant

/-! Exactly three integral-equivalence classes of full-dimensional secondary
 domains, with actual Delaunay-cell semantics and nonvacuous relative topology. -/
noncomputable section
namespace D4.Delaunay
open Analytic Matrix Set

theorem coneFamily_valenceCount_injective :
    Function.Injective (fun i : Fin 3 => valenceCount (coneFamily i) 24) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    norm_num [coneFamily, cells1_valenceCount_24, cells2_valenceCount_24,
      cells3_valenceCount_24] at h ⊢

theorem domain_image_valenceCount {V : Set SymGram} {i : Fin 3}
    (h : IsIntegralDomainImage V i) {P : SymGram} (hP : P ∈ V) :
    valenceCount (delaunayType P.1) 24=valenceCount (coneFamily i) 24 := by
  obtain ⟨U,hU,he⟩ := h
  rw [he] at hP
  have htype := ((positiveCone_eq_typeLocus i).subset hP).2
  have hcount := valenceCount_equiv
    (delaunayType ((realMatrix U)ᵀ * P.1 * realMatrix U)) (delaunayType P.1)
    (integerBasisEquiv U hU).toAddEquiv (delaunayType_basis_change P.1 U hU) 24
  change valenceCount (delaunayType (symmetricCongruence (realMatrix U) P).1) 24=
    valenceCount (delaunayType P.1) 24 at hcount
  rw [htype] at hcount
  exact hcount.symm

theorem integral_domain_image_unique {V : Set SymGram} (hV : V.Nonempty)
    {i j : Fin 3} (hi : IsIntegralDomainImage V i) (hj : IsIntegralDomainImage V j) : i=j := by
  obtain ⟨P,hP⟩ := hV
  exact coneFamily_valenceCount_injective
    ((domain_image_valenceCount hi hP).symm.trans (domain_image_valenceCount hj hP))

theorem positiveCone_integral_image_self (i : Fin 3) :
    IsIntegralDomainImage (positiveCone i) i := by
  refine ⟨1,by simp,?_⟩
  have hR : realMatrix (1 : IntegerMatrix)=1 := by
    simp [realMatrix]
  ext Q
  simp only [mem_preimage, hR, symmetricCongruence_one]

theorem positiveCone_integral_image_iff (i j : Fin 3) :
    IsIntegralDomainImage (positiveCone i) j ↔ i=j := by
  constructor
  · intro h
    exact integral_domain_image_unique (positiveCone_nonempty i)
      (positiveCone_integral_image_self i) h
  · rintro rfl
    exact positiveCone_integral_image_self i

/-- The article's full-dimensional classification: each displayed strict cone
 is a genuine maximal secondary domain, the three are inequivalent, and every
 such domain is equivalent to exactly one of them. -/
theorem exactly_three_secondary_domains :
    (∀ i : Fin 3, IsMaximalSecondaryDomain (positiveCone i)) ∧
    (∀ i j : Fin 3, IsIntegralDomainImage (positiveCone i) j ↔ i=j) ∧
    (∀ V : Set SymGram, IsMaximalSecondaryDomain V →
      ∃! i : Fin 3, IsIntegralDomainImage V i) := by
  refine ⟨positiveCone_maximal,positiveCone_integral_image_iff,?_⟩
  intro V hV
  obtain ⟨i,hi⟩ := maximal_secondary_domain_classification V hV
  exact ⟨i,hi,fun j hj => integral_domain_image_unique hV.2.1 hj hi⟩

end D4.Delaunay
