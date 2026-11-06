import D4.CompleteTheoremA
import D4.DitherMoment
import D4.ApplicationAssembly
import D4.BlockCommonScale

noncomputable section
namespace D4
open Analytic FacetGeometry MeasureTheory ProbabilityTheory

namespace Blocks
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (L : ι → Submodule ℤ Euclidean.Point)
  [∀ i, DiscreteTopology (L i)] [∀ i, IsZLattice ℝ (L i)]

/-- Sharp four-dimensional block bound, including the full equality case. -/
theorem four_dimensional_block_optimality :
    optimalConstant ≤ normalizedCellMoment (productLattice L) ∧
      (normalizedCellMoment (productLattice L) = optimalConstant ↔
        (∀ i, Euclidean.SimilarLattices (Euclidean.lattice (basisMatrix ℝ))
          (L i : Set Euclidean.Point)) ∧
        (∀ i j, volume.real (voronoi (L i)) = volume.real (voronoi (L j)))) :=
  four_dimensional_block_optimality_of_bounds L (fun i => Euclidean.geometricTheoremA (L i))

/-- Equality is exactly a common positive scale of independently rotated D4 blocks. -/
theorem four_dimensional_block_equality :
    normalizedCellMoment (productLattice L) = optimalConstant ↔
      ∃ r : ℝ, 0 < r ∧ ∃ O : ι → Euclidean.Point ≃ₗᵢ[ℝ] Euclidean.Point,
        ∀ i, (L i : Set Euclidean.Point) =
          (fun p => r • O i p) '' Euclidean.lattice (basisMatrix ℝ) :=
  (four_dimensional_block_optimality L).2.trans (similarD4_equal_volumes_iff_common_scale L)

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
theorem four_dimensional_dither_optimality :
    optimalConstant * (volume.real (voronoi L))^(1/2:ℝ) ≤
      (∫ ω, ‖ditherError L Q (X ω) (U ω)‖^2 ∂P) / 4 ∧
    ((∫ ω, ‖ditherError L Q (X ω) (U ω)‖^2 ∂P) / 4 =
      optimalConstant * (volume.real (voronoi L))^(1/2:ℝ) ↔
      Euclidean.SimilarLattices (Euclidean.lattice (basisMatrix ℝ)) (L:Set Euclidean.Point)) :=
  four_dimensional_dither_optimality_of_bound L P X U hX hU hind huniform Q hQm hQ
    (Euclidean.geometricTheoremA L)

end FacetGeometry
end D4
