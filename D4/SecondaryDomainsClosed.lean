import D4.SecondaryDomainsExactlyThree
import D4.SecondaryDomainsClosure
import D4.SecondaryDomainsCone
import D4.SecondaryDomainsSphere
import D4.SecondaryDomainsScaling

/-! Closed secondary cones, including their boundary, are the closures of the
 classified strict domains. Their interiors recover the domains exactly. -/
noncomputable section
namespace D4.Delaunay
open Analytic Principal Matrix Set Filter
open scoped Topology

theorem interior_nonnegativeCone (i : Fin 3) : interior (nonnegativeCone i)=positiveCone i := by
  apply Subset.antisymm
  · intro Q hQ k
    by_contra! hk
    let w : Fin 10 → ℝ := coneCoordinates i Q.1
    let wminus : ℕ → Fin 10 → ℝ := fun n => -(positiveApprox (-w) n)
    have hwlim : Tendsto wminus atTop (𝓝 w) := by
      simpa only [neg_neg] using (positiveApprox_tendsto (-w)).neg
    have hlim : Tendsto (fun n => coneSymForm i (wminus n)) atTop (𝓝 Q) := by
      have h := (coneHomeomorph i).continuous.tendsto w |>.comp hwlim
      have he : coneSymForm i w=Q := Subtype.ext (coneForm_coordinates i Q.1 Q.2)
      change Tendsto (fun n => coneSymForm i (wminus n)) atTop (𝓝 (coneSymForm i w)) at h
      rwa [he] at h
    obtain ⟨n,hn⟩ := (hlim.eventually (mem_interior_iff_mem_nhds.mp hQ)).exists
    have hn' : 0 ≤ wminus n k := by
      have hh := hn k
      change 0 ≤ coneCoordinates i (coneForm i (wminus n)) k at hh
      rwa [coneCoordinates_form] at hh
    have hd : 0 < 1 / ((n : ℝ)+1) := by positivity
    change 0 ≤ -(-w k+1/((n:ℝ)+1)) at hn'
    change w k ≤ 0 at hk
    linarith
  · exact interior_maximal (fun Q hQ k => (hQ k).le) (positiveCone_isOpen i)

theorem closure_integral_domain_image {V : Set SymGram} {i : Fin 3}
    (h : IsIntegralDomainImage V i) :
    ∃ U : IntegerMatrix, ∃ hU : IsUnit U.det,
      closure V=(symmetricCongruence (realMatrix U)) ⁻¹' nonnegativeCone i := by
  obtain ⟨U,hU,he⟩ := h
  let e := symmetricCongruenceHomeomorph (realMatrix U) (realMatrix_det_isUnit U hU)
  refine ⟨U,hU,?_⟩
  rw [he]
  change closure (e ⁻¹' positiveCone i)=e ⁻¹' nonnegativeCone i
  rw [← e.preimage_closure, closure_positiveCone]

theorem closed_image_recovers_domain {V : Set SymGram} {i : Fin 3}
    (h : IsIntegralDomainImage V i) : interior (closure V)=V := by
  obtain ⟨U,hU,he⟩ := h
  let e := symmetricCongruenceHomeomorph (realMatrix U) (realMatrix_det_isUnit U hU)
  rw [he]
  change interior (closure (e ⁻¹' positiveCone i))=e ⁻¹' positiveCone i
  rw [← e.preimage_closure, ← e.preimage_interior, closure_positiveCone, interior_nonnegativeCone]

/-- The closed-cone form of the classification, with unique integral type. -/
theorem exactly_three_closed_secondary_cones (V : Set SymGram)
    (hV : IsMaximalSecondaryDomain V) :
    ∃! i : Fin 3, ∃ U : IntegerMatrix, ∃ hU : IsUnit U.det,
      closure V=(symmetricCongruence (realMatrix U)) ⁻¹' nonnegativeCone i := by
  obtain ⟨i,hi,_⟩ := exactly_three_secondary_domains.2.2 V hV
  refine ⟨i,closure_integral_domain_image hi,?_⟩
  intro j hj
  obtain ⟨U,hU,he⟩ := hj
  have hre := closed_image_recovers_domain hi
  have hji : IsIntegralDomainImage V j := by
    refine ⟨U,hU,?_⟩
    let e := symmetricCongruenceHomeomorph (realMatrix U) (realMatrix_det_isUnit U hU)
    have h := congrArg interior he
    change interior (closure V)=interior (e ⁻¹' nonnegativeCone j) at h
    rw [hre,← e.preimage_interior,interior_nonnegativeCone] at h
    exact h
  exact integral_domain_image_unique hV.2.1 hji hi

end D4.Delaunay
