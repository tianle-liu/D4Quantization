import D4.VoronoiDecomposition
import D4.ConeAnalysisFacetAngle

noncomputable section
open Set MeasureTheory D4.ConeAnalysis
open scoped InnerProductSpace Topology Pointwise
namespace D4.FacetGeometry
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

theorem facetRayCone_measurable {z : E} (hz : z ≠ 0) : MeasurableSet (facetRayCone L z) := by
  rw [facetRayCone_eq_coordinates L hz]
  exact (unitJoinProduct hz).measurableEmbedding.measurableSet_image.mpr
    (heightCone_measurable (normalizedFacetBase_compact L z).measurableSet)

theorem facetRayCone_smul {z : E} (hz : z ≠ 0) {c : ℝ} (hc : 0 < c) (x : E) :
    c • x ∈ facetRayCone L z ↔ x ∈ facetRayCone L z := by
  rw [facetRayCone_eq_coordinates L hz]
  obtain ⟨p, rfl⟩ := (unitJoinProduct hz).surjective x
  rw [← unitJoinProduct_smul, (unitJoinProduct hz).injective.mem_set_image,
    (unitJoinProduct hz).injective.mem_set_image]
  exact heightCone_smul _ hc p

theorem zero_not_mem_facetRayCone {z : E} (hz : z ≠ 0) : (0:E) ∉ facetRayCone L z := by
  rw [facetRayCone_eq_coordinates L hz]
  rintro ⟨p, hp, he⟩
  have h0 : unitJoinProduct hz (0 : tangent z × ℝ) = 0 := by simp
  have hp0 : p = 0 := (unitJoinProduct hz).injective (he.trans h0.symm)
  subst p
  exact (lt_irrefl 0) hp.1

theorem facetSolidAngle_eq_cap {z : E} (hz : z ≠ 0) :
    facetSolidAngle L z = (Module.finrank ℝ E:ℝ) *
      volume.real (facetRayCone L z ∩ Metric.ball (0:E) 1) := by
  apply sphericalMeasure_eq_dim_cap volume _ (facetRayCone_measurable hz)
    (zero_not_mem_facetRayCone hz)
  exact fun c hc x => facetRayCone_smul hz hc x

theorem facetRayCone_inter_subset_tangent {z w : E} (hz : z ∈ L) (hw : w ∈ L)
    (hz0 : z ≠ 0) (hw0 : w ≠ 0) :
    facetRayCone L z ∩ facetRayCone L w ⊆
      (tangent (‖w‖^2 • z-‖z‖^2 • w) : Set E) := by
  rintro x ⟨⟨t, ht, y, hy, he⟩, ⟨s, hs, v, hv, he'⟩⟩
  change 0 < t at ht
  change 0 < s at hs
  have hp : 0 < 1+t+s := by linarith
  let c : ℝ := (1+t+s)⁻¹
  have hc : 0 < c := inv_pos.mpr hp
  have hct : c*t ≤ 1 := by
    dsimp [c]
    rw [mul_comm, ← div_eq_mul_inv]
    apply (div_le_one hp).mpr
    linarith
  have hcs : c*s ≤ 1 := by
    dsimp [c]
    rw [mul_comm, ← div_eq_mul_inv]
    apply (div_le_one hp).mpr
    linarith
  have hm : c • x ∈ closedPyramid L z ∩ closedPyramid L w := by
    constructor
    · exact ⟨c*t, ⟨mul_nonneg hc.le ht.le, hct⟩, y, hy, by rw [← he, smul_smul]⟩
    · exact ⟨c*s, ⟨mul_nonneg hc.le hs.le, hcs⟩, v, hv, by rw [← he', smul_smul]⟩
  have hn := pyramid_inter_subset_tangent hz hw hz0 hw0 hm
  have hb := (tangent (‖w‖^2 • z-‖z‖^2 • w)).smul_mem c⁻¹ hn
  simpa only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using hb

theorem facetRayCone_inter_volume_zero {z w : E} (hz : z ∈ L) (hw : w ∈ L)
    (hz0 : z ≠ 0) (hw0 : w ≠ 0) (hne : z ≠ w) :
    volume (facetRayCone L z ∩ facetRayCone L w) = 0 :=
  measure_mono_null (facetRayCone_inter_subset_tangent hz hw hz0 hw0)
    (tangent_volume_zero (face_normal_distinct hz0 hw0 hne))

theorem finite_ray_cover {T : Finset E}
    (hT : ∀ x : E, x ∈ voronoi L ↔ ∀ z ∈ T, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2)
    {x : E} (hx : x ≠ 0) : x ∈ ⋃ z ∈ T, facetRayCone L z := by
  have hn : voronoi L ∈ 𝓝 (0:E) := mem_interior_iff_mem_nhds.mp zero_mem_interior_voronoi
  have hp : 0 < gauge (voronoi L) x := (gauge_pos (absorbent_nhds_zero hn)
    (NormedSpace.isVonNBounded_of_isBounded ℝ (voronoi_compact_full (L:=L)).isBounded)).mpr hx
  have hy : (gauge (voronoi L) x)⁻¹ • x ∈ frontier (voronoi L) := by
    apply (gauge_eq_one_iff_mem_frontier (voronoi_convex L) hn).mp
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hp.le), smul_eq_mul, inv_mul_cancel₀ hp.ne']
  obtain ⟨z, hz, hyz⟩ := frontier_has_active_vector hT hy
  apply mem_iUnion.mpr
  refine ⟨z, mem_iUnion.mpr ⟨hz, ?_⟩⟩
  exact ⟨gauge (voronoi L) x, hp, _, hyz, smul_inv_smul₀ hp.ne' x⟩


theorem ray_caps_ae_ball [Nontrivial E] {T : Finset E}
    (hT : ∀ x : E, x ∈ voronoi L ↔ ∀ z ∈ T, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2) :
    Metric.ball (0:E) 1 =ᵐ[volume] ⋃ z ∈ T, facetRayCone L z ∩ Metric.ball (0:E) 1 := by
  apply ae_eq_set.mpr
  constructor
  · apply measure_mono_null (t := {(0:E)}) _ (measure_singleton 0)
    rintro x ⟨hx, hn⟩
    by_contra h0
    have hx0 : x ≠ 0 := by simpa using h0
    rcases mem_iUnion.mp (finite_ray_cover hT hx0) with ⟨z, hz⟩
    rcases mem_iUnion.mp hz with ⟨hz, hcone⟩
    exact hn (mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, hcone, hx⟩⟩)
  · have he : (⋃ z ∈ T, facetRayCone L z ∩ Metric.ball (0:E) 1) ⊆ Metric.ball (0:E) 1 := by
      intro x hx
      rcases mem_iUnion.mp hx with ⟨z, hz⟩
      rcases mem_iUnion.mp hz with ⟨_, hc⟩
      exact hc.2
    rw [diff_eq_empty.mpr he, measure_empty]

theorem sum_facetSolidAngle [Nontrivial E] {T : Finset E}
    (hmem : ∀ z ∈ T, z ∈ L ∧ z ≠ 0)
    (hT : ∀ x : E, x ∈ voronoi L ↔ ∀ z ∈ T, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2) :
    ∑ z ∈ T, facetSolidAngle L z =
      (Module.finrank ℝ E:ℝ) * volume.real (Metric.ball (0:E) 1) := by
  let S : E → Set E := fun z => facetRayCone L z ∩ Metric.ball (0:E) 1
  have hpair : Set.Pairwise (↑T) (fun z w => AEDisjoint volume (S z) (S w)) := by
    intro z hz w hw hne
    apply measure_mono_null (t := facetRayCone L z ∩ facetRayCone L w)
    · exact fun x hx => ⟨hx.1.1, hx.2.1⟩
    · exact facetRayCone_inter_volume_zero (hmem z hz).1 (hmem w hw).1
        (hmem z hz).2 (hmem w hw).2 hne
  have hmeas : ∀ z ∈ T, MeasurableSet (S z) := fun z hz =>
    (facetRayCone_measurable (hmem z hz).2).inter Metric.isOpen_ball.measurableSet
  have hfinite : ∀ z ∈ T, volume (S z) ≠ ⊤ := fun z _ =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_right)
  have hvol : volume.real (Metric.ball (0:E) 1) = ∑ z ∈ T, volume.real (S z) :=
    (measureReal_congr (ray_caps_ae_ball hT)).trans
      (measureReal_biUnion_finset₀ hpair (fun z hz => (hmeas z hz).nullMeasurableSet) hfinite)
  calc
    ∑ z ∈ T, facetSolidAngle L z =
        ∑ z ∈ T, (Module.finrank ℝ E:ℝ)*volume.real (S z) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact facetSolidAngle_eq_cap (hmem z hz).2
    _ = (Module.finrank ℝ E:ℝ)*(∑ z ∈ T, volume.real (S z)) := by rw [Finset.mul_sum]
    _ = _ := by rw [← hvol]

theorem nonfacet_solidAngle_zero {z : E} (hzL : z ∈ L) (hz : z ≠ 0)
    (hn : ¬ IsFacetVector L z) : facetSolidAngle L z = 0 := by
  have hi : interior (base L z) = ∅ := Set.not_nonempty_iff_eq_empty.mp
    (fun h => hn ⟨hzL, hz, h⟩)
  have hi' : interior (normalizedFacetBase L z) = ∅ := by
    rw [normalizedFacetBase, interior_smul₀ (inv_ne_zero (facetHeight_pos hz).ne'), hi,
      smul_set_empty]
  have hB := normalizedFacetBase_compact L z
  have hbase : volume (normalizedFacetBase L z) = 0 := by
    simpa only [frontier, hB.isClosed.closure_eq, hi', diff_empty] using
      (normalizedFacetBase_convex L z).addHaar_frontier volume
  rw [facetSolidAngle_eq_base_integral L hz]
  exact setIntegral_zero_measure _ hbase

theorem sum_selected_facetSolidAngle [Nontrivial E] {T : Finset E}
    (hmem : ∀ z ∈ T, z ∈ L ∧ z ≠ 0)
    (hT : ∀ x : E, x ∈ voronoi L ↔ ∀ z ∈ T, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2) :
    ∑ z ∈ T.filter (IsFacetVector L), facetSolidAngle L z =
      (Module.finrank ℝ E:ℝ) * volume.real (Metric.ball (0:E) 1) := by
  rw [← sum_facetSolidAngle hmem hT, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs with h
  · rfl
  · exact (nonfacet_solidAngle_zero (hmem z hz).1 (hmem z hz).2 h).symm

end D4.FacetGeometry
