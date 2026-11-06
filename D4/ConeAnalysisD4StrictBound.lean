import D4.ConeAnalysisD4StrictFacet
import D4.ConeAnalysisStrictAssembly
import D4.GeometricTheoremB
import D4.EuclideanMoment
import D4.LatticeInfimum

/-! The strict D4 facet-count bound obtained from the actual octahedral
geometry, followed by finite Jensen and the true Voronoi decomposition. -/
noncomputable section
namespace D4.PhysicalD4
open Set MeasureTheory Euclidean FacetGeometry ConeAnalysis
attribute [local instance] Classical.propDecidable

/-- The original geometric strictness argument, independent of numerical
estimates for the circular-cone profile or the exact D4 moment value. -/
theorem geometric_twentyFour_bound_strict :
    dimensionalConeBound 4 24 < FacetGeometry.normalizedCellMoment lattice := by
  have hdim : Module.finrank ℝ Point=4 := by simp [Point]
  have hd : 2 ≤ Module.finrank ℝ Point := by omega
  have hm : (Nat.card (FacetVectors lattice):ℝ) ≤ (24:ℝ) := by rw [card_facets]; norm_num
  letI : Nontrivial Point := Module.finrank_pos_iff.mp (show 0 < Module.finrank ℝ Point by omega)
  obtain ⟨T, hmem, hT⟩ := exists_finite_voronoi_halfspaces_full (L:=lattice)
  let S := T.filter (IsFacetVector lattice)
  have hangle : ∑ z ∈ S, facetSolidAngle lattice z =
      (Module.finrank ℝ Point:ℝ)*dimensionBallVolume (Module.finrank ℝ Point) := by
    rw [← unitBall_volume_eq_dimension (F:=Point)]
    exact sum_selected_facetSolidAngle hmem hT
  have hA : 0 < (Module.finrank ℝ Point:ℝ)*dimensionBallVolume (Module.finrank ℝ Point) :=
    mul_pos (by exact_mod_cast (show 0 < Module.finrank ℝ Point by omega)) (dimensionBallVolume_pos _)
  have hS : S.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hangle
    linarith
  have hfacet : ∀ z ∈ S, IsFacetVector lattice z := fun z hz => (Finset.mem_filter.mp hz).2
  have hcard : (S.card:ℝ) ≤ (24:ℝ) :=
    (show (S.card:ℝ) ≤ (Nat.card (FacetVectors lattice):ℝ) by
      exact_mod_cast selected_facets_card_le hmem).trans hm
  have H := finite_normalized_bound_card_le_strict S hS (Module.finrank ℝ Point) hd
    (dimensionBallVolume (Module.finrank ℝ Point-1))
    ((Module.finrank ℝ Point:ℝ)*dimensionBallVolume (Module.finrank ℝ Point)) (24:ℝ)
    (dimensionBallVolume_pos _) (fun z => volume.real (FacetGeometry.pyramid lattice z))
    (fun z => ∫ x in FacetGeometry.pyramid lattice z, ‖x‖^2) (facetSolidAngle lattice)
    (fun z hz => facet_pyramid_volume_pos (hfacet z hz))
    (fun z hz => facet_pyramid_secondMoment_pos (hfacet z hz))
    (fun z hz => facetSolidAngle_mem_dimension (hfacet z hz) hd)
    hangle hcard (fun z hz => facet_pyramid_dimension_comparison_strict (hfacet z hz) hd
      (normalized_facet_base_radial_nonconstant (hfacet z hz)))
  rw [← voronoi_volume_eq_sum_facets hmem hT,
    ← voronoi_secondMoment_eq_sum_facets hmem hT] at H
  change dimensionalConeBound (Module.finrank ℝ Point) 24 < FacetGeometry.normalizedCellMoment lattice at H
  simpa only [hdim] using H

theorem voronoi_eq_basis_cell :
    voronoi lattice=Euclidean.cell (basisMatrix ℝ) := by
  ext p
  change (∀ q∈(lattice:Set Point), ‖p‖≤‖p-q‖) ↔
    ∀ q∈Euclidean.lattice (basisMatrix ℝ), ‖p‖≤‖p-q‖
  rw [lattice_eq_basis_lattice]

theorem physical_normalizedCellMoment_eq_basis :
    FacetGeometry.normalizedCellMoment lattice=
      Euclidean.normalizedCellMoment (basisMatrix ℝ) := by
  unfold FacetGeometry.normalizedCellMoment ConePerspective.normalizedMoment
    Euclidean.normalizedCellMoment
  rw [voronoi_eq_basis_cell]
  norm_num [Point,measureReal_def]

/-- Strict comparison for the article's physical lattice, derived from
its facets rather than from an independent profile estimate. -/
theorem geometric_basis_twentyFour_bound_strict :
    dimensionalConeBound 4 24 < Euclidean.normalizedCellMoment (basisMatrix ℝ) := by
  rw [← physical_normalizedCellMoment_eq_basis]
  exact geometric_twentyFour_bound_strict

theorem geometric_gram_twentyFour_bound_strict :
    dimensionalConeBound 4 24 < Analytic.normalizedMoment (gramMatrix ℝ) := by
  have h := geometric_basis_twentyFour_bound_strict
  rw [Euclidean.normalizedCellMoment_eq (by rw [det_basisMatrix]; norm_num),
    Euclidean.gram,basisMatrix_transpose_mul] at h
  exact h

/-- The complete displayed D4 chain, now obtained by the geometric
strictness argument and monotonicity in the actual facet count. -/
theorem geometric_final_cone_chain :
    dimensionalConeBound 4 30 ≤ dimensionalConeBound 4 24 ∧
      dimensionalConeBound 4 24 < Euclidean.normalizedCellMoment (basisMatrix ℝ) := by
  refine ⟨?_,geometric_basis_twentyFour_bound_strict⟩
  have hdim : Module.finrank ℝ Point=4 := by simp [Point]
  have h := dimensionalConeBound_facet_count_comparison lattice (by omega : 2 ≤ Module.finrank ℝ Point)
  simpa only [hdim,card_facets,Nat.reducePow,Nat.reduceSub,Nat.reduceMul,Nat.cast_ofNat] using h

end D4.PhysicalD4
