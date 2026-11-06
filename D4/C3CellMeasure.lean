import D4.C3CellCertificates
import D4.C3CellDetCertificates
import D4.C3CellGeometryVolumes
import D4.C23CellPositivity
import D4.C23CellVolume
import D4.C23DeterminantEvaluation
import D4.PrincipalSimplexMomentCertificate
set_option maxHeartbeats 0
noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal Certificate CertificateMoments MeasureTheory

theorem c3_cell_det_eval (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (t : Fin 582) :
    eval (extendWeight w) (c3CellDetPoly t) = (simplexMatrix (c3CellVertices w t)).det := by
  rw [← c3_det_polynomial t]
  exact cellFactorProduct_eval c3IntegerGenerators c3VertexCoefficients c3FacetNormal
    w (c3Cell t) (c3DetCoordinate t) (c3DetSign t)
    (c3_support_rows t).2.1 (c3_support_rows t).1 (c3_cell_geometry w hw t)

theorem c3_cell_det_pos (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (t : Fin 582) :
    0 < (simplexMatrix (c3CellVertices w t)).det := by
  exact cell_simplex_det_pos c3IntegerGenerators c3VertexCoefficients c3FacetNormal
    w (c3Cell t) (c3DetCoordinate t) (c3DetSign t) hw
    (secondary_posDef_of_pos _ (hw 0) (fun j => (hw j.succ).le))
    (c3_facet_normals_ne_zero _) (c3_support_rows t).2.1 (c3_support_rows t).1
    (c3_cell_geometry w hw t) (c3_support_rows t).2.2.1 (c3_support_rows t).2.2.2

theorem c3_cell_abs_det (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) (t : Fin 582) :
    |(simplexMatrix (c3CellVertices w t)).det| = eval (extendWeight w) (c3CellDetPoly t) := by
  rw [abs_of_pos (c3_cell_det_pos w hw t),c3_cell_det_eval w hw t]

theorem c3_cell_volume_polynomial (x : Nat → ℝ) :
    (∑ t, eval x (c3CellDetPoly t)) = 384 * eval x determinantC3 := by
  have h := cellVolumeFull_eval c3CellDetPoly c3CellBatches c3_cell_batches_partition x
  have hh : eval x (sumFast [c3GeometryVolumePart0,c3GeometryVolumePart1,c3GeometryVolumePart2,c3GeometryVolumePart3,c3GeometryVolumePart4,c3GeometryVolumePart5,c3GeometryVolumePart6,c3GeometryVolumePart7,c3GeometryVolumePart8,c3GeometryVolumePart9,c3GeometryVolumePart10,c3GeometryVolumePart11,c3GeometryVolumePart12,c3GeometryVolumePart13,c3GeometryVolumePart14,c3GeometryVolumePart15,c3GeometryVolumePart16,c3GeometryVolumePart17,c3GeometryVolumePart18,c3GeometryVolumePart19,c3GeometryVolumePart20,c3GeometryVolumePart21,c3GeometryVolumePart22,c3GeometryVolumePart23,c3GeometryVolumePart24,c3GeometryVolumePart25,c3GeometryVolumePart26,c3GeometryVolumePart27,c3GeometryVolumePart28,c3GeometryVolumePart29]) =
      ∑ t, eval x (c3CellDetPoly t) := by
    simpa (config := {implicitDefEqProofs := false}) only [c3CellBatches,List.map_cons,List.map_nil,
      c3GeometryVolumePart0_check,
      c3GeometryVolumePart1_check,
      c3GeometryVolumePart2_check,
      c3GeometryVolumePart3_check,
      c3GeometryVolumePart4_check,
      c3GeometryVolumePart5_check,
      c3GeometryVolumePart6_check,
      c3GeometryVolumePart7_check,
      c3GeometryVolumePart8_check,
      c3GeometryVolumePart9_check,
      c3GeometryVolumePart10_check,
      c3GeometryVolumePart11_check,
      c3GeometryVolumePart12_check,
      c3GeometryVolumePart13_check,
      c3GeometryVolumePart14_check,
      c3GeometryVolumePart15_check,
      c3GeometryVolumePart16_check,
      c3GeometryVolumePart17_check,
      c3GeometryVolumePart18_check,
      c3GeometryVolumePart19_check,
      c3GeometryVolumePart20_check,
      c3GeometryVolumePart21_check,
      c3GeometryVolumePart22_check,
      c3GeometryVolumePart23_check,
      c3GeometryVolumePart24_check,
      c3GeometryVolumePart25_check,
      c3GeometryVolumePart26_check,
      c3GeometryVolumePart27_check,
      c3GeometryVolumePart28_check,
      c3GeometryVolumePart29_check] using h
  rw [c3_geometry_volume_polynomial,eval_scale] at hh
  simpa only [Int.cast_ofNat] using hh.symm

theorem c3_cell_volume_sum (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    (∑ t, |(simplexMatrix (c3CellVertices w t)).det|) =
      384*(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)).det := by
  simp only [c3_cell_abs_det w hw]
  rw [c3_cell_volume_polynomial,determinantC3_extendWeight_eval]

theorem c3_simplex_moment_actual (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    simplexMomentNumerator (secondaryForm cone3Vectors (w 0) (fun j => w j.succ))
      (c3CellVertices w) =
      46080*(secondaryForm cone3Vectors (w 0) (fun j => w j.succ)).det^2 *
        moment (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) := by
  exact simplexMomentNumerator_eq_actual
    (secondary_posDef_of_pos _ (hw 0) (fun j => (hw j.succ).le)) (c3CellVertices w)
    (fun t => (c3_cell_det_pos w hw t).ne') (c3_cells_support w hw)
    (c3_cells_pairwise_null w hw) (c3_cell_volume_sum w hw)

end D4.Secondary
