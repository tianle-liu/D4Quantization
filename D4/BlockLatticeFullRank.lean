import D4.BlockEuclidean

/-! The Euclidean orthogonal product really is a discrete full-rank lattice. -/
noncomputable section
namespace D4.Blocks
open Set
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (L : ι → Submodule ℤ (EuclideanSpace ℝ κ))

def productLatticeHomeomorph : (∀ i, L i) ≃ₜ productLattice L where
  toFun x := ⟨blockJoin (fun i => (x i : EuclideanSpace ℝ κ)),
    (blockJoin_mem_productLattice L _).mpr (fun i => (x i).property)⟩
  invFun x i := ⟨blockJoin.symm (x : EuclideanSpace ℝ (ι × κ)) i,
    (blockJoin_mem_productLattice L _).mp (by simpa using x.property) i⟩
  left_inv x := by ext i; simp
  right_inv x := by apply Subtype.ext; simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (blockJoin (ι:=ι) (κ:=κ)).toContinuousLinearEquiv.continuous.comp
      (continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i)))
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (continuous_apply i).comp
      ((blockJoin (ι:=ι) (κ:=κ)).toContinuousLinearEquiv.symm.continuous.comp continuous_subtype_val)

instance productLattice_discrete [∀ i, DiscreteTopology (L i)] :
    DiscreteTopology (productLattice L) :=
  (productLatticeHomeomorph L).symm.isEmbedding.discreteTopology

instance productLattice_isZLattice [∀ i, DiscreteTopology (L i)]
    [∀ i, IsZLattice ℝ (L i)] : IsZLattice ℝ (productLattice L) where
  span_top := by
    classical
    let T := Submodule.span ℝ (productLattice L : Set (EuclideanSpace ℝ (ι × κ)))
    let f (i : ι) : EuclideanSpace ℝ κ →ₗ[ℝ] EuclideanSpace ℝ (ι × κ) :=
      blockJoin.toLinearMap.comp (LinearMap.single ℝ (fun _ : ι => EuclideanSpace ℝ κ) i)
    have hli (i : ι) : Submodule.span ℝ (L i : Set (EuclideanSpace ℝ κ)) ≤ T.comap (f i) := by
      apply Submodule.span_le.mpr
      intro z hz
      apply Submodule.subset_span
      change blockJoin (Pi.single i z) ∈ productLattice L
      apply (blockJoin_mem_productLattice L _).mpr
      intro j
      by_cases hji : j=i
      · subst j; simpa [f] using hz
      · simp [Pi.single_apply,hji]
    have hi (i : ι) (z : EuclideanSpace ℝ κ) : f i z ∈ T := by
      have h := hli i
      rw [IsZLattice.span_top] at h
      exact h (Submodule.mem_top : z ∈ (⊤ : Submodule ℝ (EuclideanSpace ℝ κ)))
    apply top_unique
    intro x _
    have he : x = ∑ i, f i (blockJoin.symm x i) := by
      apply blockJoin.symm.injective
      simp only [map_sum]
      ext i j
      simp [f, LinearMap.single_apply, Pi.single_apply]
    rw [he]
    exact Submodule.sum_mem T (fun i _ => hi i _)

end D4.Blocks
