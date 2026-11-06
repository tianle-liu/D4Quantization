import D4.EuclideanSimilarity
import D4.DitherMoment
import D4.BlockLatticeMoment

noncomputable section
namespace D4
open Analytic FacetGeometry MeasureTheory ProbabilityTheory

namespace Blocks
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (L : ι → Submodule ℤ Euclidean.Point)
  [∀ i, DiscreteTopology (L i)] [∀ i, IsZLattice ℝ (L i)]

/-- Sharp four-dimensional block bound, including the full equality case. -/
theorem four_dimensional_block_optimality_of_bounds
    (hA : ∀ i, optimalConstant ≤ normalizedCellMoment (L i) ∧
      (normalizedCellMoment (L i) = optimalConstant ↔
        Euclidean.SimilarLattices (Euclidean.lattice (basisMatrix ℝ))
          (L i : Set Euclidean.Point))) :
    optimalConstant ≤ normalizedCellMoment (productLattice L) ∧
      (normalizedCellMoment (productLattice L) = optimalConstant ↔
        (∀ i, Euclidean.SimilarLattices (Euclidean.lattice (basisMatrix ℝ))
          (L i : Set Euclidean.Point)) ∧
        (∀ i j, volume.real (voronoi (L i)) = volume.real (voronoi (L j)))) := by
  have h := normalizedCellMoment_product_lower_eq L optimalConstant optimalConstant_pos
    (fun i => (hA i).1)
  refine ⟨h.1, h.2.trans ?_⟩
  apply and_congr_left
  intro _
  exact forall_congr' fun i => (hA i).2
end Blocks

namespace FacetGeometry
variable (L : Submodule ℤ Euclidean.Point) [DiscreteTopology L] [IsZLattice ℝ L]
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X U : Ω → Euclidean.Point) (hX : Measurable X) (hU : Measurable U)
  (hind : IndepFun X U P) (huniform : P.map U = uniformVoronoi L)
  (Q : Euclidean.Point → L) (hQm : Measurable Q)
  (hQ : ∀ x, x-(Q x:Euclidean.Point) ∈ voronoi L)

include hX hU hind huniform hQm hQ in
/-- At fixed volume, the dither MSE is minimized exactly by D4 similarities. -/
theorem four_dimensional_dither_optimality_of_bound
    (hA : optimalConstant ≤ normalizedCellMoment L ∧
      (normalizedCellMoment L = optimalConstant ↔
        Euclidean.SimilarLattices (Euclidean.lattice (basisMatrix ℝ))
          (L : Set Euclidean.Point))) :
    optimalConstant * (volume.real (voronoi L))^(1/2:ℝ) ≤
      (∫ ω, ‖ditherError L Q (X ω) (U ω)‖^2 ∂P) / 4 ∧
    ((∫ ω, ‖ditherError L Q (X ω) (U ω)‖^2 ∂P) / 4 =
      optimalConstant * (volume.real (voronoi L))^(1/2:ℝ) ↔
      Euclidean.SimilarLattices (Euclidean.lattice (basisMatrix ℝ)) (L:Set Euclidean.Point)) := by
  have h := subtractive_dither_distortion L P X U hX hU hind huniform Q hQm hQ
    (by simp [Euclidean.Point])
  norm_num [Euclidean.Point] at h
  rw [h]
  have hv : 0 < (volume.real (voronoi L))^(1/2:ℝ) :=
    Real.rpow_pos_of_pos (ENNReal.toReal_pos (voronoi_volume_pos L).ne'
      (voronoi_compact_full (L:=L)).measure_ne_top) _
  exact ⟨mul_le_mul_of_nonneg_right hA.1 hv.le,
    (mul_left_inj' hv.ne').trans hA.2⟩
end FacetGeometry
end D4
