import D4.BlockLatticeFullRank
import D4.BlockMomentAlgebra
import D4.GeometricTheoremB

/-! Actual Voronoi integrals and the exact product formula for orthogonal
lattice blocks. -/
noncomputable section
namespace D4.Blocks
open MeasureTheory Set FacetGeometry
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (L : ι → Submodule ℤ (EuclideanSpace ℝ κ))

theorem product_voronoi_volume :
    volume.real (voronoi (productLattice L)) = ∏ i, volume.real (voronoi (L i)) := by
  rw [product_voronoi]
  have h := blockJoin_measurePreserving.measure_preimage_emb
    blockJoinMeasurable.measurableEmbedding
    (blockJoin '' univ.pi (fun i => voronoi (L i)))
  have he : blockJoin ⁻¹' (blockJoin '' univ.pi (fun i => voronoi (L i))) =
      univ.pi (fun i => voronoi (L i)) :=
    Set.preimage_image_eq _ blockJoin.injective
  rw [he] at h
  change (volume (blockJoin '' univ.pi (fun i => voronoi (L i)))).toReal = _
  rw [← h]
  exact volume_real_pi _

variable [∀ i, DiscreteTopology (L i)] [∀ i, IsZLattice ℝ (L i)]

theorem block_voronoi_volume_pos (i : ι) : 0 < volume.real (voronoi (L i)) := by
  exact ENNReal.toReal_pos
    (volume.measure_pos_of_nonempty_interior ⟨0, zero_mem_interior_voronoi (L:=L i)⟩).ne'
    (voronoi_compact_full (L:=L i)).measure_lt_top.ne

theorem product_voronoi_secondMoment [DecidableEq ι] :
    (∫ x in voronoi (productLattice L), ‖x‖^2) =
      ∑ i, (∫ y in voronoi (L i), ‖y‖^2) *
        ∏ j ∈ Finset.univ.erase i, volume.real (voronoi (L j)) := by
  rw [product_voronoi, blockJoin_measurePreserving.setIntegral_image_emb
    blockJoinMeasurable.measurableEmbedding]
  simp_rw [blockJoin_norm_sq]
  exact integral_pi_sum _ (fun i => (voronoi_closed (L i)).measurableSet)
    (fun i => (voronoi_compact_full (L:=L i)).measure_lt_top)
    (fun _ y => ‖y‖^2)
    (fun i => (continuous_norm.pow 2).continuousOn.integrableOn_compact (voronoi_compact_full (L:=L i)))

theorem normalizedCellMoment_product [Nonempty ι] [Nonempty κ] [DecidableEq ι] :
    normalizedCellMoment (productLattice L) =
      blockNormalizedMoment (Fintype.card κ)
        (fun i => normalizedCellMoment (L i)) (fun i => volume.real (voronoi (L i))) := by
  unfold normalizedCellMoment
  rw [product_voronoi_volume, product_voronoi_secondMoment]
  simp only [finrank_euclideanSpace, Fintype.card_prod, Nat.cast_mul]
  exact normalizedMoment_product_formula _ _ _
    (by exact_mod_cast Fintype.card_pos (α:=κ)) (block_voronoi_volume_pos L)

theorem normalizedCellMoment_product_lower_eq [Nonempty ι] [Nonempty κ] [DecidableEq ι]
    (b : ℝ) (hb : 0 < b) (hg : ∀ i, b ≤ normalizedCellMoment (L i)) :
    b ≤ normalizedCellMoment (productLattice L) ∧
      (normalizedCellMoment (productLattice L) = b ↔
        (∀ i, normalizedCellMoment (L i) = b) ∧
        (∀ i j, volume.real (voronoi (L i)) = volume.real (voronoi (L j)))) := by
  rw [normalizedCellMoment_product]
  exact blockNormalizedMoment_lower_eq _ _ _ b
    (by exact_mod_cast Fintype.card_pos (α:=κ)) (block_voronoi_volume_pos L) hb hg

end D4.Blocks
