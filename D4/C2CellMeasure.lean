import D4.C2CellCertificates
import D4.C2CellDetCertificates
import D4.C2CellGeometryVolumes
import D4.C23CellPositivity
import D4.C23CellVolume
import D4.C23DeterminantEvaluation
import D4.PrincipalSimplexMomentCertificate
set_option maxHeartbeats 0
noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal Certificate CertificateMoments MeasureTheory

theorem c2_cell_det_eval (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (t : Fin 580) :
    eval (extendWeight w) (c2CellDetPoly t) = (simplexMatrix (c2CellVertices w t)).det := by
  rw [← c2_det_polynomial t]
  exact cellFactorProduct_eval c2IntegerGenerators c2VertexCoefficients c2FacetNormal
    w (c2Cell t) (c2DetCoordinate t) (c2DetSign t)
    (c2_support_rows t).2.1 (c2_support_rows t).1 (c2_cell_geometry w hw t)

theorem c2_cell_det_pos (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (t : Fin 580) :
    0 < (simplexMatrix (c2CellVertices w t)).det := by
  exact cell_simplex_det_pos c2IntegerGenerators c2VertexCoefficients c2FacetNormal
    w (c2Cell t) (c2DetCoordinate t) (c2DetSign t) hw
    (secondary_posDef_of_pos _ (hw 0) (fun j => (hw j.succ).le))
    (c2_facet_normals_ne_zero _) (c2_support_rows t).2.1 (c2_support_rows t).1
    (c2_cell_geometry w hw t) (c2_support_rows t).2.2.1 (c2_support_rows t).2.2.2

theorem c2_cell_abs_det (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (t : Fin 580) :
    |(simplexMatrix (c2CellVertices w t)).det| = eval (extendWeight w) (c2CellDetPoly t) := by
  rw [abs_of_pos (c2_cell_det_pos w hw t),c2_cell_det_eval w hw t]

theorem c2_cell_volume_polynomial (x : Nat → ℝ) :
    (∑ t, eval x (c2CellDetPoly t)) = 384 * eval x determinantC2 := by
  have h := cellVolumeFull_eval c2CellDetPoly c2CellBatches c2_cell_batches_partition x
  have hh : eval x (sumFast [c2GeometryVolumePart0,c2GeometryVolumePart1,c2GeometryVolumePart2,c2GeometryVolumePart3,c2GeometryVolumePart4,c2GeometryVolumePart5,c2GeometryVolumePart6,c2GeometryVolumePart7,c2GeometryVolumePart8,c2GeometryVolumePart9,c2GeometryVolumePart10,c2GeometryVolumePart11,c2GeometryVolumePart12,c2GeometryVolumePart13,c2GeometryVolumePart14,c2GeometryVolumePart15,c2GeometryVolumePart16,c2GeometryVolumePart17,c2GeometryVolumePart18,c2GeometryVolumePart19,c2GeometryVolumePart20,c2GeometryVolumePart21,c2GeometryVolumePart22,c2GeometryVolumePart23,c2GeometryVolumePart24,c2GeometryVolumePart25,c2GeometryVolumePart26,c2GeometryVolumePart27,c2GeometryVolumePart28]) =
      ∑ t, eval x (c2CellDetPoly t) := by
    simpa (config := {implicitDefEqProofs := false}) only [c2CellBatches,List.map_cons,List.map_nil,
      c2GeometryVolumePart0_check,
      c2GeometryVolumePart1_check,
      c2GeometryVolumePart2_check,
      c2GeometryVolumePart3_check,
      c2GeometryVolumePart4_check,
      c2GeometryVolumePart5_check,
      c2GeometryVolumePart6_check,
      c2GeometryVolumePart7_check,
      c2GeometryVolumePart8_check,
      c2GeometryVolumePart9_check,
      c2GeometryVolumePart10_check,
      c2GeometryVolumePart11_check,
      c2GeometryVolumePart12_check,
      c2GeometryVolumePart13_check,
      c2GeometryVolumePart14_check,
      c2GeometryVolumePart15_check,
      c2GeometryVolumePart16_check,
      c2GeometryVolumePart17_check,
      c2GeometryVolumePart18_check,
      c2GeometryVolumePart19_check,
      c2GeometryVolumePart20_check,
      c2GeometryVolumePart21_check,
      c2GeometryVolumePart22_check,
      c2GeometryVolumePart23_check,
      c2GeometryVolumePart24_check,
      c2GeometryVolumePart25_check,
      c2GeometryVolumePart26_check,
      c2GeometryVolumePart27_check,
      c2GeometryVolumePart28_check] using h
  rw [c2_geometry_volume_polynomial,eval_scale] at hh
  simpa only [Int.cast_ofNat] using hh.symm

theorem c2_cell_volume_sum (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    (∑ t, |(simplexMatrix (c2CellVertices w t)).det|) =
      384*(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).det := by
  simp only [c2_cell_abs_det w hw]
  rw [c2_cell_volume_polynomial,determinantC2_extendWeight_eval]

theorem c2_simplex_moment_actual (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    simplexMomentNumerator (secondaryForm cone2Vectors (w 0) (fun j => w j.succ))
      (c2CellVertices w) =
      46080*(secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).det^2 *
        moment (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) := by
  exact simplexMomentNumerator_eq_actual
    (secondary_posDef_of_pos _ (hw 0) (fun j => (hw j.succ).le)) (c2CellVertices w)
    (fun t => (c2_cell_det_pos w hw t).ne') (c2_cells_support w hw)
    (c2_cells_pairwise_null w hw) (c2_cell_volume_sum w hw)

end D4.Secondary
