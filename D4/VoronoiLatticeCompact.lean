import D4.VoronoiFacetCount

/-! Compact full-dimensional cells and compact facet bases for arbitrary full lattices. -/
noncomputable section
open Set Module
open scoped InnerProductSpace
namespace D4.FacetGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

theorem voronoi_norm_le_basis {x : E} (hx : x ∈ voronoi L) :
    ‖x‖ ≤ ∑ i, ‖((b i : L) : E)‖ := by
  let br := b.ofZLatticeBasis ℝ L
  have hz : (ZSpan.floor br x : E) ∈ L := by
    have h := (ZSpan.floor br x).property
    simpa only [br, Basis.ofZLatticeBasis_span] using h
  have hn := (hx _ hz).trans (ZSpan.norm_fract_le br x)
  simpa only [br, Basis.ofZLatticeBasis_apply] using hn

include b

theorem voronoi_bounded : Bornology.IsBounded (voronoi L) :=
  isBounded_iff_forall_norm_le.mpr ⟨∑ i, ‖((b i : L) : E)‖, fun _ hx => voronoi_norm_le_basis b hx⟩

theorem voronoi_compact : IsCompact (voronoi L) :=
  Metric.isCompact_of_isClosed_isBounded (voronoi_closed L) (voronoi_bounded b)

theorem base_compact (z : E) : IsCompact (base L z) := by
  have hc : IsClosed (base L z) :=
    (voronoi_closed L).preimage (continuous_const.add continuous_subtype_val)
  apply Metric.isCompact_of_isClosed_isBounded hc
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(∑ i, ‖((b i : L) : E)‖) + ‖(1/2 : ℝ) • z‖, ?_⟩
  intro y hy
  have h := voronoi_norm_le_basis b hy
  have he : (y:E) = ((1/2 : ℝ) • z + (y:E)) - (1/2 : ℝ) • z := by abel
  change ‖(y:E)‖ ≤ _
  calc
    ‖(y:E)‖ = ‖((1/2 : ℝ) • z + (y:E)) - (1/2 : ℝ) • z‖ := congrArg norm he
    _ ≤ ‖(1/2 : ℝ) • z + (y:E)‖ + ‖(1/2 : ℝ) • z‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add_right h _

omit b in
theorem exists_lattice_separation : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ L, z ≠ (0:E) → ε ≤ ‖z‖ := by
  obtain ⟨ε, hε, hs⟩ := Metric.isOpen_iff.mp (isOpen_discrete ({0} : Set L)) 0 (by simp)
  refine ⟨ε, hε, ?_⟩
  intro z hz hz0
  by_contra! hn
  have hb : (⟨z, hz⟩ : L) ∈ Metric.ball 0 ε := by
    simpa only [Metric.mem_ball, dist_zero_right, Submodule.norm_coe] using hn
  have he := hs hb
  have hzero : (⟨z, hz⟩ : L) = 0 := Set.mem_singleton_iff.mp he
  exact hz0 (congrArg (fun v : L => (v:E)) hzero)

omit b in
theorem zero_mem_interior_voronoi : (0:E) ∈ interior (voronoi L) := by
  obtain ⟨ε, hε, hs⟩ := exists_lattice_separation (L := L)
  apply mem_interior_iff_mem_nhds.mpr
  apply Metric.mem_nhds_iff.mpr
  refine ⟨ε/2, half_pos hε, ?_⟩
  intro x hx
  have hxn : ‖x‖ < ε/2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  rw [mem_voronoi_iff]
  intro z hz
  by_cases hz0 : z = 0
  · simp [hz0]
  · have hzn := hs z hz hz0
    have hi := real_inner_le_norm x z
    have hp : 0 ≤ ‖z‖ * (‖z‖-2*‖x‖) := mul_nonneg (norm_nonneg _) (by linarith)
    nlinarith

omit b in
theorem tangent_eq_orthogonal (z : E) : tangent z = (ℝ ∙ z)ᗮ := by
  ext y
  rw [mem_tangent, Submodule.mem_orthogonal_singleton_iff_inner_right]

omit b in
theorem tangent_finrank {z : E} (hz : z ≠ 0) :
    finrank ℝ (tangent z) + 1 = finrank ℝ E := by
  rw [tangent_eq_orthogonal]
  have h := (ℝ ∙ z).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hz] at h
  omega

omit b in
theorem voronoi_compact_full : IsCompact (voronoi L) := by
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  exact voronoi_compact (Module.Free.chooseBasis ℤ L)

omit b in
theorem base_compact_full (z : E) : IsCompact (base L z) := by
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  exact base_compact (Module.Free.chooseBasis ℤ L) z

omit b in
theorem card_facetVectors_le_finrank :
    Nat.card (FacetVectors L) ≤ 2 * (2 ^ finrank ℝ E - 1) := by
  classical
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b := Module.Free.chooseBasis ℤ L
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = finrank ℝ E :=
    (Module.finrank_eq_card_basis (b.ofZLatticeBasis ℝ L)).symm
  simpa only [hc] using card_facetVectors_le b

end D4.FacetGeometry
