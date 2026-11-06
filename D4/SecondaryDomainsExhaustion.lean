import D4.SecondaryDomainsTopology
import D4.Classification
import D4.BasisChange

/-! Every nonempty open set of positive-definite symmetric forms meets an
 integral translate of one of the three strict cones. This upgrades closed
 coverage by an actual positive-parameter perturbation in the correct topology. -/
noncomputable section
namespace D4.Delaunay
open Analytic Principal Matrix Set Filter
open scoped Topology

theorem closed_coverage_coordinates (Q : SymGram) (hQ : Q.1.PosDef) :
    ∃ U : IntegerMatrix, ∃ hU : IsUnit U.det, ∃ i : Fin 3, ∃ w : Fin 10 → ℝ,
      (∀ k, 0 ≤ w k) ∧ symmetricCongruence (realMatrix U) Q=coneSymForm i w := by
  obtain ⟨R,⟨U,hU,hR⟩,hcone⟩ := secondaryConeCoverage Q.1 hQ
  rcases hcone with ⟨w,hw,he⟩ | ⟨a,w,ha,hw,he⟩ | ⟨a,w,ha,hw,he⟩
  · exact ⟨U,hU,0,w,hw,Subtype.ext (hR.symm.trans he)⟩
  · refine ⟨U,hU,1,Fin.cons a w,?_,Subtype.ext (hR.symm.trans he)⟩
    intro k
    exact Fin.cases ha hw k
  · refine ⟨U,hU,2,Fin.cons a w,?_,Subtype.ext (hR.symm.trans he)⟩
    intro k
    exact Fin.cases ha hw k

theorem open_set_meets_strict_cone (V : Set SymGram) (hV : IsOpen V)
    (Q : SymGram) (hQV : Q ∈ V) (hQ : Q.1.PosDef) :
    ∃ P ∈ V, ∃ U : IntegerMatrix, ∃ hU : IsUnit U.det, ∃ i : Fin 3,
      symmetricCongruence (realMatrix U) P ∈ positiveCone i := by
  obtain ⟨U,hU,i,w,hw,heq⟩ := closed_coverage_coordinates Q hQ
  let e := symmetricCongruenceHomeomorph (realMatrix U) (realMatrix_det_isUnit U hU)
  have hlim : Tendsto (fun n => e.symm (coneSymForm i (positiveApprox w n))) atTop (𝓝 Q) := by
    have h := e.symm.continuous.tendsto (coneSymForm i w) |>.comp
      ((coneHomeomorph i).continuous.tendsto w |>.comp (positiveApprox_tendsto w))
    have hh : e.symm (coneSymForm i w)=Q := by
      rw [← heq]
      exact e.symm_apply_apply Q
    simpa only [hh] using h
  obtain ⟨n,hn⟩ := (hlim.eventually (hV.mem_nhds hQV)).exists
  refine ⟨e.symm (coneSymForm i (positiveApprox w n)),hn,U,hU,i,?_⟩
  change e (e.symm (coneSymForm i (positiveApprox w n))) ∈ positiveCone i
  rw [e.apply_symm_apply]
  change ∀ k, 0 < coneCoordinates i (coneForm i (positiveApprox w n)) k
  rw [coneCoordinates_form]
  exact positiveApprox_pos hw n

end D4.Delaunay
