import D4.SecondaryDomainsSourceCones

/-! The greatest-open-locus definition is equivalent to ordinary inclusion
 maximality among all nonempty open positive-definite constant-type domains. -/
noncomputable section
namespace D4.Delaunay
open Set

/-- A nonempty open positive-definite locus with one actual Delaunay type.
The type is arbitrary and is not restricted to a displayed family. -/
def IsSecondaryDomain (U : Set SymGram) : Prop :=
  IsOpen U ∧ U.Nonempty ∧ ∃ T : Set (Finset Analytic.IntVec), U ⊆ typeLocus T

/-- Ordinary maximality by inclusion, allowing the type of the competing
 domain to be specified independently. -/
def IsInclusionMaximalSecondaryDomain (U : Set SymGram) : Prop :=
  IsSecondaryDomain U ∧ ∀ V : Set SymGram, IsSecondaryDomain V → U ⊆ V → V=U

theorem maximal_secondary_domain_iff_inclusion_maximal (U : Set SymGram) :
    IsMaximalSecondaryDomain U ↔ IsInclusionMaximalSecondaryDomain U := by
  constructor
  · rintro ⟨hopen,hne,T,hsub,hmax⟩
    refine ⟨⟨hopen,hne,T,hsub⟩,?_⟩
    rintro V ⟨hvopen,hvne,S,hvsub⟩ huv
    obtain ⟨Q,hQ⟩ := hne
    have hTS : T=S := (hsub hQ).2.symm.trans (hvsub (huv hQ)).2
    subst S
    exact Subset.antisymm (hmax V hvopen hvsub) huv
  · rintro ⟨⟨hopen,hne,T,hsub⟩,hmax⟩
    refine ⟨hopen,hne,T,hsub,?_⟩
    intro V hvopen hvsub
    have hUV : IsSecondaryDomain (U∪V) :=
      ⟨hopen.union hvopen,hne.mono subset_union_left,T,union_subset hsub hvsub⟩
    have he := hmax (U∪V) hUV subset_union_left
    exact he ▸ subset_union_right

/-- The exact-three classification also holds with the usual inclusion
 maximality statement as its only domain hypothesis. -/
theorem exactly_three_inclusion_maximal_secondary_domains (U : Set SymGram)
    (hU : IsInclusionMaximalSecondaryDomain U) :
    ∃! i : Fin 3, IsIntegralDomainImage U i :=
  exactly_three_secondary_domains.2.2 U
    ((maximal_secondary_domain_iff_inclusion_maximal U).mpr hU)

end D4.Delaunay
