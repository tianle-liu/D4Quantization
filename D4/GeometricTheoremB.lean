import D4.VoronoiRayPartition
import D4.ConeAnalysisDimension
import D4.ConeAnalysisAssembly

/-! Theorem B for the actual Voronoi cell of every full-rank Euclidean
lattice. The facet partition, its integrals and angles, the individual
cone comparisons and the parity count are all proved from the library. -/
noncomputable section
namespace D4.FacetGeometry
open Set MeasureTheory D4.ConeAnalysis
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def normalizedCellMoment (L : Submodule ℤ E) : ℝ :=
  ConePerspective.normalizedMoment (Module.finrank ℝ E)
    (volume.real (voronoi L)) (∫ x in voronoi L, ‖x‖^2)

def dimensionalConeBound (d : ℕ) (m : ℝ) : ℝ :=
  m^(-2/(d:ℝ)) * coneNormalizedMoment d (dimensionBallVolume (d-1))
    (((d:ℝ)*dimensionBallVolume d)/m)

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem geometric_facet_bound (hd : 2 ≤ Module.finrank ℝ E) (m : ℝ)
    (hm : (Nat.card (FacetVectors L):ℝ) ≤ m) :
    dimensionalConeBound (Module.finrank ℝ E) m ≤ normalizedCellMoment L := by
  letI : Nontrivial E := Module.finrank_pos_iff.mp (show 0 < Module.finrank ℝ E by omega)
  obtain ⟨T, hmem, hT⟩ := exists_finite_voronoi_halfspaces_full (L:=L)
  let S := T.filter (IsFacetVector L)
  have hangle : ∑ z ∈ S, facetSolidAngle L z =
      (Module.finrank ℝ E:ℝ)*dimensionBallVolume (Module.finrank ℝ E) := by
    rw [← unitBall_volume_eq_dimension (F:=E)]
    exact sum_selected_facetSolidAngle hmem hT
  have hA : 0 < (Module.finrank ℝ E:ℝ)*dimensionBallVolume (Module.finrank ℝ E) :=
    mul_pos (by exact_mod_cast (show 0 < Module.finrank ℝ E by omega)) (dimensionBallVolume_pos _)
  have hS : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hangle
    linarith
  have hfacet : ∀ z ∈ S, IsFacetVector L z := fun z hz => (Finset.mem_filter.mp hz).2
  have hcard : (S.card:ℝ) ≤ m :=
    (show (S.card:ℝ) ≤ (Nat.card (FacetVectors L):ℝ) by
      exact_mod_cast selected_facets_card_le hmem).trans hm
  have H := finite_normalized_bound_card_le S hS (Module.finrank ℝ E) hd
    (dimensionBallVolume (Module.finrank ℝ E-1))
    ((Module.finrank ℝ E:ℝ)*dimensionBallVolume (Module.finrank ℝ E)) m
    (dimensionBallVolume_pos _) (fun z => volume.real (pyramid L z))
    (fun z => ∫ x in pyramid L z, ‖x‖^2) (facetSolidAngle L)
    (fun z hz => facet_pyramid_volume_pos (hfacet z hz))
    (fun z hz => facet_pyramid_secondMoment_pos (hfacet z hz))
    (fun z hz => facetSolidAngle_mem_dimension (hfacet z hz) hd)
    hangle hcard (fun z hz => facet_pyramid_dimension_comparison (hfacet z hz) hd)
  rw [← voronoi_volume_eq_sum_facets hmem hT,
    ← voronoi_secondMoment_eq_sum_facets hmem hT] at H
  exact H

/-- The bound using the actual number of Voronoi facets. -/
theorem theoremB_actual_facets (hd : 2 ≤ Module.finrank ℝ E) :
    dimensionalConeBound (Module.finrank ℝ E) (Nat.card (FacetVectors L)) ≤
      normalizedCellMoment L :=
  geometric_facet_bound L hd _ le_rfl

/-- The dimension-only bound of Theorem B. No geometric or analytic
hypotheses are assumed beyond being a full-rank lattice in dimension ≥ 2. -/
theorem theoremB (hd : 2 ≤ Module.finrank ℝ E) :
    dimensionalConeBound (Module.finrank ℝ E) (2*(2^Module.finrank ℝ E-1):ℕ) ≤
      normalizedCellMoment L :=
  geometric_facet_bound L hd _ (by exact_mod_cast card_facetVectors_le_finrank (L:=L))

end D4.FacetGeometry
