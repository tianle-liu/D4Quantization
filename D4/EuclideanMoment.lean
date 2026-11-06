import D4.EuclideanSemantics
import D4.VoronoiCompact
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Euclidean Voronoi volume and second moment

The region is defined by the actual Euclidean norm and all points of the
integer-image lattice. Its physical Lebesgue volume and integral are related
to the Gram-coordinate quantities by a proved change of variables.
-/
noncomputable section
open Matrix MeasureTheory Set
open scoped ENNReal

namespace D4.Euclidean
open Analytic

def coordinateEquiv (B : Gram) (hB : B.det ≠ 0) : Vec ≃ₗ[ℝ] Vec :=
  { B.mulVecLin with
    invFun := B⁻¹.mulVec
    left_inv := fun x => by
      change B⁻¹ *ᵥ (B *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB),
        Matrix.one_mulVec]
    right_inv := fun x => by
      change B *ᵥ (B⁻¹ *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB),
        Matrix.one_mulVec] }

def realizationEquiv (B : Gram) (hB : B.det ≠ 0) : Vec ≃L[ℝ] Point :=
  (coordinateEquiv B hB).toContinuousLinearEquiv.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm

@[simp] theorem realizationEquiv_apply (B : Gram) (hB : B.det ≠ 0) (x : Vec) :
    realizationEquiv B hB x = realization B x := rfl

def realizationMeasurableEquiv (B : Gram) (hB : B.det ≠ 0) : Vec ≃ᵐ Point :=
  (realizationEquiv B hB).toHomeomorph.toMeasurableEquiv

@[simp] theorem realizationMeasurableEquiv_apply (B : Gram) (hB : B.det ≠ 0) (x : Vec) :
    realizationMeasurableEquiv B hB x = realization B x := rfl

theorem gram_posDef_of_det_ne_zero {B : Gram} (hB : B.det ≠ 0) : (gram B).PosDef :=
  gram_posDef B (coordinateEquiv B hB).injective

/-- The physical Voronoi cell, using all lattice points and the Euclidean norm. -/
def cell (B : Gram) : Set Point :=
  {p | ∀ q ∈ lattice B, ‖p‖ ≤ ‖p-q‖}

theorem realization_mem_cell_iff (B : Gram) (x : Vec) :
    realization B x ∈ cell B ↔ x ∈ voronoi (gram B) := by
  constructor
  · intro hx z
    have h := hx _ (show realization B (castVec z) ∈ lattice B from ⟨z, rfl⟩)
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
    simpa only [← realization_sub, norm_sq_realization] using hs
  · intro hx q hq
    obtain ⟨z, rfl⟩ := hq
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [← realization_sub, norm_sq_realization] using hx z

theorem realization_preimage_cell (B : Gram) :
    realization B ⁻¹' cell B = voronoi (gram B) :=
  Set.ext (realization_mem_cell_iff B)

theorem cell_eq_image_voronoi {B : Gram} (hB : B.det ≠ 0) :
    cell B = realization B '' voronoi (gram B) := by
  rw [← realization_preimage_cell]
  exact ((realizationEquiv B hB).surjective.image_preimage (cell B)).symm

theorem cell_compact {B : Gram} (hB : B.det ≠ 0) : IsCompact (cell B) := by
  rw [cell_eq_image_voronoi hB]
  exact (voronoi_compact (gram_posDef_of_det_ne_zero hB)).image (realizationEquiv B hB).continuous

theorem squared_norm_integrableOn_cell {B : Gram} (hB : B.det ≠ 0) :
    IntegrableOn (fun p : Point => ‖p‖^2) (cell B) :=
  (continuous_norm.pow 2).continuousOn.integrableOn_compact (cell_compact hB)

/-- The physical Jacobian is the absolute determinant of the basis matrix. -/
theorem map_realization_volume {B : Gram} (hB : B.det ≠ 0) :
    Measure.map (realization B) volume = ENNReal.ofReal |B.det|⁻¹ • volume := by
  have hm : Measurable (Matrix.toLin' B) :=
    (coordinateEquiv B hB).toContinuousLinearEquiv.continuous.measurable
  change Measure.map ((WithLp.equiv 2 Vec).symm ∘ Matrix.toLin' B) volume = _
  rw [← Measure.map_map (PiLp.volume_preserving_equiv_symm (Fin 4)).measurable hm,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hB, Measure.map_smul,
    (PiLp.volume_preserving_equiv_symm (Fin 4)).map_eq]
  rw [abs_inv]

/-- The Euclidean Voronoi volume equals the covolume of the displayed basis. -/
theorem cell_volume {B : Gram} (hB : B.det ≠ 0) :
    volume (cell B) = ENNReal.ofReal |B.det| := by
  have h := congrArg (fun μ : Measure Point => μ (cell B)) (map_realization_volume hB)
  change (Measure.map (realization B) volume) (cell B) =
    (ENNReal.ofReal |B.det|⁻¹ • volume) (cell B) at h
  have hm : Measurable (realization B) := (realizationEquiv B hB).continuous.measurable
  rw [Measure.map_apply hm
      (cell_compact hB).measurableSet, realization_preimage_cell,
    voronoi_volume (gram_posDef_of_det_ne_zero hB)] at h
  simp only [Measure.smul_apply, smul_eq_mul] at h
  have hd : (ENNReal.ofReal |B.det| : ℝ≥0∞) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (abs_pos.mpr hB))
  rw [ENNReal.ofReal_inv_of_pos (abs_pos.mpr hB)] at h
  calc
    volume (cell B) = ENNReal.ofReal |B.det| *
        ((ENNReal.ofReal |B.det|)⁻¹ * volume (cell B)) :=
      (ENNReal.mul_inv_cancel_left hd ENNReal.ofReal_ne_top).symm
    _ = ENNReal.ofReal |B.det| := by rw [← h, mul_one]

/-- Exact equality of the physical Voronoi integral and the Gram integral. -/
theorem cell_second_moment {B : Gram} (hB : B.det ≠ 0) :
    (∫ p in cell B, ‖p‖^2) = |B.det| * moment (gram B) := by
  have h := setIntegral_map_equiv (μ := (volume : Measure Vec))
    (realizationMeasurableEquiv B hB) (fun p : Point => ‖p‖^2) (cell B)
  change (∫ p in cell B, ‖p‖^2 ∂Measure.map (realization B) volume) =
    (∫ x in realization B ⁻¹' cell B, ‖realization B x‖^2) at h
  rw [map_realization_volume hB, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)), smul_eq_mul,
    realization_preimage_cell] at h
  simp_rw [norm_sq_realization] at h
  rw [← moment_eq_voronoi (gram_posDef_of_det_ne_zero hB)] at h
  calc
    (∫ p in cell B, ‖p‖^2) = |B.det| * (|B.det|⁻¹ * (∫ p in cell B, ‖p‖^2)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hB), one_mul]
    _ = |B.det| * moment (gram B) := by rw [h]

/-- The article's dimension-four normalization using the actual cell volume. -/
def normalizedCellMoment (B : Gram) : ℝ :=
  (∫ p in cell B, ‖p‖^2) / (4 * (volume (cell B)).toReal ^ (3/2 : ℝ))

/-- The geometric normalized moment is exactly the Gram-coordinate quantity. -/
theorem normalizedCellMoment_eq {B : Gram} (hB : B.det ≠ 0) :
    normalizedCellMoment B = normalizedMoment (gram B) := by
  have hd : (gram B).det = |B.det|^2 := by
    rw [gram, Matrix.det_mul, Matrix.det_transpose, sq_abs]
    ring
  have hq : (|B.det|^2) ^ (1/4 : ℝ) = |B.det| ^ (1/2 : ℝ) := by
    rw [← Real.rpow_natCast |B.det| 2, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have ht : |B.det| ^ (3/2 : ℝ) = |B.det| * |B.det| ^ (1/2 : ℝ) := by
    rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num,
      Real.rpow_add (abs_pos.mpr hB), Real.rpow_one]
  unfold normalizedCellMoment normalizedMoment
  rw [cell_second_moment hB, cell_volume hB, ENNReal.toReal_ofReal (abs_nonneg _), hd, hq, ht]
  field_simp [abs_ne_zero.mpr hB,
    (Real.rpow_pos_of_pos (abs_pos.mpr hB) (1/2 : ℝ)).ne']
  ring

end D4.Euclidean
