import D4.ConeAnalysisFacet

/-! Bisector faces that are not facets contribute zero actual volume. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory D4.FacetGeometry
open scoped Pointwise

theorem nonfacet_pyramid_volume_zero {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E}
    [DiscreteTopology L] [IsZLattice ℝ L] {z : E}
    (hzL : z ∈ L) (hz : z ≠ 0) (hn : ¬ IsFacetVector L z) :
    volume (D4.FacetGeometry.pyramid L z) = 0 := by
  have hi : interior (base L z) = ∅ := Set.not_nonempty_iff_eq_empty.mp
    (fun h => hn ⟨hzL, hz, h⟩)
  have hi' : interior (normalizedFacetBase L z) = ∅ := by
    rw [normalizedFacetBase, interior_smul₀ (inv_ne_zero (facetHeight_pos hz).ne'), hi,
      smul_set_empty]
  have hB := normalizedFacetBase_compact L z
  have hbase : volume (normalizedFacetBase L z) = 0 := by
    simpa only [frontier, hB.isClosed.closure_eq, hi', diff_empty] using
      (normalizedFacetBase_convex L z).addHaar_frontier volume
  have hreal : volume.real (D4.FacetGeometry.pyramid L z) = 0 := by
    rw [facet_pyramid_volume L hz]
    obtain ⟨M, hM, hb⟩ := hB.isBounded.subset_closedBall_lt 0 (0 : tangent z)
    rw [pyramid_volume volume hB.measurableSet hM.le hb]
    simp [measureReal_def, hbase]
  have hfinite : volume (D4.FacetGeometry.pyramid L z) ≠ ⊤ :=
    ne_top_of_le_ne_top (closedPyramid_compact z).measure_lt_top.ne
      (measure_mono (pyramid_subset_closedPyramid L z))
  exact ((ENNReal.toReal_eq_zero_iff _).mp hreal).resolve_right hfinite

end D4.ConeAnalysis
