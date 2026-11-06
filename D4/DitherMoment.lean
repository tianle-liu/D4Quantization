import D4.DitherProbability
import D4.GeometricTheoremB

noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace D4.FacetGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem uniformVoronoi_secondMoment :
    (∫ x, ‖x‖^2 ∂uniformVoronoi L) =
      (∫ x in voronoi L, ‖x‖^2) / volume.real (voronoi L) := by
  simp only [uniformVoronoi, integral_smul_measure, ENNReal.toReal_inv,
    smul_eq_mul, measureReal_def, div_eq_mul_inv, mul_comm]

theorem uniformVoronoi_distortion (hd : 0 < Module.finrank ℝ E) :
    (∫ x, ‖x‖^2 ∂uniformVoronoi L) / (Module.finrank ℝ E:ℝ) =
      normalizedCellMoment L * (volume.real (voronoi L))^(2/(Module.finrank ℝ E:ℝ)) := by
  have hv : 0 < volume.real (voronoi L) :=
    ENNReal.toReal_pos (voronoi_volume_pos L).ne' (voronoi_compact_full (L := L)).measure_ne_top
  have hd' : (Module.finrank ℝ E:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [uniformVoronoi_secondMoment, normalizedCellMoment, ConePerspective.normalizedMoment,
    Real.rpow_add hv, Real.rpow_one]
  field_simp [hv.ne', hd', (Real.rpow_pos_of_pos hv (2/(Module.finrank ℝ E:ℝ))).ne']
  ring

theorem subtractive_dither_distortion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X U : Ω → E)
    (hX : Measurable X) (hU : Measurable U) (hind : IndepFun X U P)
    (huniform : P.map U = uniformVoronoi L)
    (Q : E → L) (hQm : Measurable Q) (hQ : ∀ x, x-(Q x:E) ∈ voronoi L)
    (hd : 0 < Module.finrank ℝ E) :
    (∫ ω, ‖ditherError L Q (X ω) (U ω)‖^2 ∂P) / (Module.finrank ℝ E:ℝ) =
      normalizedCellMoment L * (volume.real (voronoi L))^(2/(Module.finrank ℝ E:ℝ)) := by
  have hm := (subtractive_dither_independent L P X U hX hU hind huniform Q hQm hQ).1
  have he : Measurable (fun ω => ditherError L Q (X ω) (U ω)) :=
    ((measurable_subtype_coe.comp (hQm.comp (hX.add hU))).sub hU).sub hX
  rw [← integral_map_of_stronglyMeasurable he (continuous_norm.pow 2).stronglyMeasurable, hm]
  exact uniformVoronoi_distortion L hd

theorem subtractive_dither_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X U : Ω → E)
    (hX : Measurable X) (hU : Measurable U) (hind : IndepFun X U P)
    (huniform : P.map U = uniformVoronoi L)
    (Q : E → L) (hQm : Measurable Q) (hQ : ∀ x, x-(Q x:E) ∈ voronoi L)
    (hd : 2 ≤ Module.finrank ℝ E) :
    dimensionalConeBound (Module.finrank ℝ E) (2*((2:ℕ)^Module.finrank ℝ E-1):ℕ) *
      (volume.real (voronoi L))^(2/(Module.finrank ℝ E:ℝ)) ≤
    (∫ ω, ‖ditherError L Q (X ω) (U ω)‖^2 ∂P) / (Module.finrank ℝ E:ℝ) := by
  rw [subtractive_dither_distortion L P X U hX hU hind huniform Q hQm hQ (by omega)]
  exact mul_le_mul_of_nonneg_right (theoremB L hd) (Real.rpow_nonneg (by positivity) _)

end D4.FacetGeometry
