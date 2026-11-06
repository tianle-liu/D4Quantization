import D4.VoronoiFacetGeometry

/-! Facet vectors are the unique opposite shortest pair in their parity class. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace D4.FacetGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem functional_zero_of_base {L : Submodule ℤ E} {z u : E} (hz : IsFacetVector L z)
    (h : ∀ y ∈ base L z, ⟪(y:E),u⟫_ℝ = 0) (y : tangent z) : ⟪(y:E),u⟫_ℝ = 0 := by
  let f : tangent z →ₗ[ℝ] ℝ := (innerSL ℝ u).toLinearMap.comp (tangent z).subtype
  have hs : base L z ⊆ (LinearMap.ker f : Set (tangent z)) := by
    intro v hv
    change ⟪u,(v:E)⟫_ℝ = 0
    rw [real_inner_comm]
    exact h v hv
  have ht : LinearMap.ker f = ⊤ :=
    (LinearMap.ker f).eq_top_of_nonempty_interior'
      (hz.2.2.mono (interior_mono hs))
  have hy : y ∈ LinearMap.ker f := by rw [ht]; trivial
  change ⟪u,(y:E)⟫_ℝ = 0 at hy
  rwa [real_inner_comm] at hy

theorem facet_orthogonal_decomposition {L : Submodule ℤ E} {z u v : E}
    (hz : IsFacetVector L z) (hu : u ∈ L) (hv : v ∈ L)
    (he : z = u+v) (ho : ⟪u,v⟫_ℝ = 0) : u = 0 ∨ v = 0 := by
  by_contra h
  push_neg at h
  have hou : ⟪v,u⟫_ℝ = 0 := by rwa [real_inner_comm]
  have hb (y : tangent z) (hy : y ∈ base L z) : ⟪(y:E),u⟫_ℝ = 0 := by
    have hp := (mem_voronoi_iff L _).mp hy u hu
    have hm := (mem_voronoi_iff L _).mp ((neg_mem_base_iff hz.1 y).mpr hy) u hu
    simp only [he, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hou, Submodule.coe_neg, inner_neg_left] at hp hm
    linarith
  let t : E := ‖v‖^2 • u - ‖u‖^2 • v
  have ht : t ∈ tangent z := by
    rw [mem_tangent, he]
    dsimp [t]
    simp only [inner_add_left, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, ho, hou]
    ring
  have hf := functional_zero_of_base hz hb ⟨t, ht⟩
  change ⟪t,u⟫_ℝ = 0 at hf
  dsimp [t] at hf
  simp only [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hou,
    mul_zero, sub_zero] at hf
  have hp : 0 < ‖v‖^2 * ‖u‖^2 :=
    mul_pos (sq_pos_of_pos (norm_pos_iff.mpr h.2)) (sq_pos_of_pos (norm_pos_iff.mpr h.1))
  linarith

def SameParity (L : Submodule ℤ E) (z w : E) : Prop :=
  ∃ u ∈ L, z-w = (2 : ℤ) • u

theorem sameParity_refl (L : Submodule ℤ E) (z : E) : SameParity L z z :=
  ⟨0, L.zero_mem, by simp⟩

theorem sameParity_symm {L : Submodule ℤ E} {z w : E} (h : SameParity L z w) :
    SameParity L w z := by
  obtain ⟨u, hu, he⟩ := h
  refine ⟨-u, L.neg_mem hu, ?_⟩
  rw [smul_neg, ← he]
  abel

/-- There is no different shortest competitor in the parity class of a facet vector. -/
theorem facet_shortest_unique_pair {L : Submodule ℤ E} {z w : E}
    (hz : IsFacetVector L z) (hp : SameParity L z w) (hn : ‖w‖ ≤ ‖z‖) :
    w = z ∨ w = -z := by
  obtain ⟨u, hu, he⟩ := hp
  let v : E := z-u
  have hv : v ∈ L := L.sub_mem hz.1 hu
  have hzuv : z = u+v := by dsimp [v]; abel
  have hw : w = v-u := by
    rw [show (2 : ℤ) • u = u+u by simp [two_smul]] at he
    dsimp [v]
    have hzz : z = u+u+w := sub_eq_iff_eq_add.mp he
    rw [hzz]
    abel
  have huv : ⟪v,u⟫_ℝ = ⟪u,v⟫_ℝ := real_inner_comm u v
  have hc := (mem_voronoi_iff L _).mp (facet_center_mem hz) u hu
  rw [hzuv, real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq,
    huv] at hc
  have hs : ‖w‖^2 ≤ ‖z‖^2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
  rw [hw, hzuv, norm_sub_sq_real, norm_add_sq_real, huv] at hs
  have ho : ⟪u,v⟫_ℝ = 0 := by linarith
  rcases facet_orthogonal_decomposition hz hu hv hzuv ho with h | h
  · left
    rw [h, zero_add] at hzuv
    simpa only [h, sub_zero, ← hzuv] using hw
  · right
    rw [h, add_zero] at hzuv
    simpa only [h, zero_sub, ← hzuv] using hw

theorem facet_not_zero_parity {L : Submodule ℤ E} {z : E} (hz : IsFacetVector L z) :
    ¬ SameParity L z 0 := by
  intro h
  rcases facet_shortest_unique_pair hz h (by simp) with h | h
  · exact hz.2.1 h.symm
  · exact hz.2.1 (neg_eq_zero.mp h.symm)

theorem facets_sameParity_eq_or_neg {L : Submodule ℤ E} {z w : E}
    (hz : IsFacetVector L z) (hw : IsFacetVector L w) (hp : SameParity L z w) :
    w = z ∨ w = -z := by
  rcases le_total ‖w‖ ‖z‖ with hn | hn
  · exact facet_shortest_unique_pair hz hp hn
  · rcases facet_shortest_unique_pair hw (sameParity_symm hp) hn with h | h
    · exact Or.inl h.symm
    · right
      rw [h, neg_neg]

end D4.FacetGeometry
