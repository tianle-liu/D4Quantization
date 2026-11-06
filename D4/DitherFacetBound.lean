import D4.DitherMoment

noncomputable section
namespace D4.FacetGeometry
open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem subtractive_dither_facet_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X U : Ω → E)
    (hX : Measurable X) (hU : Measurable U) (hind : IndepFun X U P)
    (huniform : P.map U = uniformVoronoi L)
    (Q : E → L) (hQm : Measurable Q) (hQ : ∀ x, x-(Q x:E) ∈ voronoi L)
    (hd : 2 ≤ Module.finrank ℝ E) :
    dimensionalConeBound (Module.finrank ℝ E) (Nat.card (FacetVectors L)) *
      (volume.real (voronoi L))^(2/(Module.finrank ℝ E:ℝ)) ≤
    (∫ ω, ‖ditherError L Q (X ω) (U ω)‖^2 ∂P) / (Module.finrank ℝ E:ℝ) := by
  rw [subtractive_dither_distortion L P X U hX hU hind huniform Q hQm hQ (by omega)]
  exact mul_le_mul_of_nonneg_right (theoremB_actual_facets L hd)
    (Real.rpow_nonneg (by positivity) _)

end D4.FacetGeometry
