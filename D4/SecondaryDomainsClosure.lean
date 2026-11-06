import D4.SecondaryDomainsTopology

/-! The closed generator cones are precisely the closures of the strict
secondary domains, in the relative topology of symmetric Gram matrices. -/
noncomputable section
namespace D4.Delaunay
open Analytic Principal Matrix Set Filter Topology

def nonnegativeCone (i : Fin 3) : Set SymGram :=
  {Q | ∀ k, 0 ≤ coneCoordinates i Q.1 k}

theorem nonnegativeCone_isClosed (i : Fin 3) : IsClosed (nonnegativeCone i) := by
  have h : nonnegativeCone i=⋂ k : Fin 10, {Q : SymGram | 0 ≤ coneCoordinates i Q.1 k} := by
    ext Q
    simp [nonnegativeCone]
  rw [h]
  apply isClosed_iInter
  intro k
  exact isClosed_le continuous_const
    ((continuous_apply k).comp ((coneCoordinates_continuous i).comp continuous_subtype_val))

theorem closure_positiveCone (i : Fin 3) : closure (positiveCone i)=nonnegativeCone i := by
  apply subset_antisymm
  · apply closure_minimal
    · intro Q hQ k
      exact (hQ k).le
    · exact nonnegativeCone_isClosed i
  · intro Q hQ
    let w : Fin 10 → ℝ := coneCoordinates i Q.1
    have hform : coneSymForm i w=Q :=
      Subtype.ext (coneForm_coordinates i Q.1 Q.2)
    have ht : Tendsto (fun n => coneSymForm i (positiveApprox w n)) atTop (𝓝 Q) := by
      have h := (coneHomeomorph i).continuous.tendsto w |>.comp (positiveApprox_tendsto w)
      change Tendsto (fun n => coneSymForm i (positiveApprox w n)) atTop
        (𝓝 (coneSymForm i w)) at h
      rwa [hform] at h
    apply mem_closure_of_tendsto ht
    apply Eventually.of_forall
    intro n
    change ∀ k, 0 < coneCoordinates i (coneForm i (positiveApprox w n)) k
    rw [coneCoordinates_form]
    exact positiveApprox_pos hQ n

end D4.Delaunay
