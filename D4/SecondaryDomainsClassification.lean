import D4.SecondaryDomainsExhaustion
import D4.SecondaryDomainsTransport
import D4.SecondaryDomainsPosDef

/-! Exhaustiveness for actual maximal open Delaunay domains. -/
noncomputable section
namespace D4.Delaunay
open Analytic Matrix Set

/-- An actual open secondary domain, up to an integral change of basis. -/
def IsIntegralDomainImage (V : Set SymGram) (i : Fin 3) : Prop :=
  ∃ U : IntegerMatrix, ∃ hU : IsUnit U.det,
    V=(symmetricCongruence (realMatrix U)) ⁻¹' positiveCone i

/-- Every maximal full-dimensional secondary domain is one of the three
 displayed strict cones after an actual integral basis change. -/
theorem maximal_secondary_domain_classification (V : Set SymGram)
    (hV : IsMaximalSecondaryDomain V) : ∃ i : Fin 3, IsIntegralDomainImage V i := by
  obtain ⟨hopen,⟨Q,hQV⟩,T,hsub,hmax⟩ := hV
  obtain ⟨P,hPV,U,hU,i,hi⟩ := open_set_meets_strict_cone V hopen Q hQV (hsub hQV).1
  let e := symmetricCongruenceHomeomorph (realMatrix U) (realMatrix_det_isUnit U hU)
  have hPi : delaunayType (symmetricCongruence (realMatrix U) P).1=coneFamily i :=
    ((positiveCone_eq_typeLocus i).subset hi).2
  have htype (R : SymGram) : delaunayType R.1=T ↔
      delaunayType (symmetricCongruence (realMatrix U) R).1=coneFamily i := by
    have h := delaunayType_congruence_eq_iff R.1 P.1 U hU
    change (delaunayType (symmetricCongruence (realMatrix U) R).1=
      delaunayType (symmetricCongruence (realMatrix U) P).1) ↔
      (delaunayType R.1=delaunayType P.1) at h
    rw [hPi,(hsub hPV).2] at h
    exact h.symm
  let W : Set SymGram := (symmetricCongruence (realMatrix U)) ⁻¹' positiveCone i
  have hWopen : IsOpen W := (positiveCone_isOpen i).preimage
    (symmetricCongruence_continuous _)
  have hWsub : W ⊆ typeLocus T := by
    intro R hR
    have hr := (positiveCone_eq_typeLocus i).subset hR
    exact ⟨(symmetricCongruence_posDef_iff R U hU).mp hr.1,(htype R).mpr hr.2⟩
  have hVW : V ⊆ W := by
    intro R hR
    apply (positiveCone_eq_typeLocus i).superset
    exact ⟨(symmetricCongruence_posDef_iff R U hU).mpr (hsub hR).1,
      (htype R).mp (hsub hR).2⟩
  exact ⟨i,U,hU,Subset.antisymm hVW (hmax W hWopen hWsub)⟩

end D4.Delaunay
