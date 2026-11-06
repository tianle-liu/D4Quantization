import D4.PrincipalIntegral
import D4.PrincipalVoronoi

/-!
# Actual moment and volume in principal dual coordinates

The change of variables is `r = 2 Q x`. All equalities refer to the true
integer-nearest-point integral and Lebesgue measure.
-/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

private theorem dual_det {Q : Gram} (hQ : Q.PosDef) :
    ((2 : ℝ) • Q).det = 16 * Q.det := by
  rw [Matrix.det_smul]
  norm_num

private theorem dual_det_pos {Q : Gram} (hQ : Q.PosDef) : 0 < ((2 : ℝ) • Q).det := by
  rw [dual_det hQ]
  exact mul_pos (by norm_num) hQ.det_pos

theorem zonotope_volume {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e)
    (hQ : (principalForm w).PosDef) :
    volume (zonotope w) = ENNReal.ofReal (16 * (principalForm w).det) := by
  let Q := principalForm w
  have hQ0 : Q.PosDef := hQ
  have hB : ((2 : ℝ) • Q).det ≠ 0 := (dual_det_pos hQ).ne'
  have hp : (fun x : Vec => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) ⁻¹' zonotope w = voronoi Q := by
    simpa only [zero_add, Matrix.smul_mulVec_assoc] using (voronoi_eq_zonotope_preimage hw).symm
  have hm : Measurable (fun x : Vec => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) :=
    (affineMeasurableEquiv ((2 : ℝ) • Q) hB 0).measurable
  have h := congrArg (fun μ : Measure Vec => μ (zonotope w)) (map_affine_volume ((2 : ℝ) • Q) hB 0)
  change (Measure.map (fun x : Vec => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) volume) (zonotope w) =
    (ENNReal.ofReal |((2 : ℝ) • Q).det|⁻¹ • volume) (zonotope w) at h
  rw [Measure.map_apply hm (zonotope_isCompact w).measurableSet,
    hp, voronoi_volume hQ] at h
  simp only [Measure.smul_apply, smul_eq_mul] at h
  rw [abs_of_pos (dual_det_pos hQ0), ENNReal.ofReal_inv_of_pos (dual_det_pos hQ0)] at h
  have hn : ENNReal.ofReal ((2 : ℝ) • Q).det ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (dual_det_pos hQ))
  calc
    volume (zonotope w) = ENNReal.ofReal ((2 : ℝ) • Q).det *
        ((ENNReal.ofReal ((2 : ℝ) • Q).det)⁻¹ * volume (zonotope w)) :=
      (ENNReal.mul_inv_cancel_left hn ENNReal.ofReal_ne_top).symm
    _ = ENNReal.ofReal ((2 : ℝ) • Q).det := by rw [← h, mul_one]
    _ = _ := by rw [dual_det hQ]

theorem quadratic_inverse_dual {Q : Gram} (hQ : Q.PosDef) (x : Vec) :
    quadratic Q⁻¹ (((2 : ℝ) • Q) *ᵥ x) = 4 * quadratic Q x := by
  rw [Matrix.smul_mulVec_assoc, quadratic_smul_vec]
  have hi : Q⁻¹ *ᵥ (Q *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hQ.det_pos.ne'),
      Matrix.one_mulVec]
  have hh : quadratic Q⁻¹ (Q *ᵥ x) = quadratic Q x := by
    unfold quadratic
    rw [hi, dotProduct_comm]
  rw [hh]
  norm_num

set_option maxHeartbeats 1000000 in
/-- Actual dual-coordinate integral, before replacing the inverse by adjugate. -/
theorem zonotope_inverse_moment {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e)
    (hQ : (principalForm w).PosDef) :
    (∫ r in zonotope w, quadratic (principalForm w)⁻¹ r) =
      64 * (principalForm w).det * moment (principalForm w) := by
  let Q := principalForm w
  have hQ0 : Q.PosDef := hQ
  have hB : ((2 : ℝ) • Q).det ≠ 0 := (dual_det_pos hQ).ne'
  have hp : (fun x : Vec => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) ⁻¹' zonotope w = voronoi Q := by
    simpa only [zero_add, Matrix.smul_mulVec_assoc] using (voronoi_eq_zonotope_preimage hw).symm
  have h := setIntegral_map_equiv (μ := (volume : Measure Vec))
    (affineMeasurableEquiv ((2 : ℝ) • Q) hB 0) (quadratic Q⁻¹) (zonotope w)
  change (∫ r in zonotope w, quadratic Q⁻¹ r ∂Measure.map (fun x => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) volume) =
    (∫ x in (fun x => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) ⁻¹' zonotope w,
      quadratic Q⁻¹ (0 + ((2 : ℝ) • Q) *ᵥ x)) at h
  rw [map_affine_volume ((2 : ℝ) • Q) hB 0, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)), smul_eq_mul,
    abs_of_pos (dual_det_pos hQ), hp] at h
  simp_rw [zero_add, quadratic_inverse_dual hQ0] at h
  rw [integral_const_mul, ← moment_eq_voronoi hQ, dual_det hQ] at h
  change (∫ r in zonotope w, quadratic Q⁻¹ r) = 64 * Q.det * moment Q
  have hd : Q.det ≠ 0 := hQ.det_pos.ne'
  calc
    (∫ r in zonotope w, quadratic Q⁻¹ r) =
        (16 * Q.det) * ((16 * Q.det)⁻¹ * (∫ r in zonotope w, quadratic Q⁻¹ r)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (by norm_num) hd), one_mul]
    _ = (16 * Q.det) * (4 * moment Q) := by rw [h]
    _ = _ := by ring

/-- The adjugate form of the actual dual-coordinate moment identity. -/
theorem zonotope_adjugate_moment {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e)
    (hQ : (principalForm w).PosDef) :
    (∫ r in zonotope w, quadratic (principalForm w).adjugate r) =
      64 * (principalForm w).det^2 * moment (principalForm w) := by
  have hi := zonotope_inverse_moment hw hQ
  rw [Matrix.inv_def, Ring.inverse_eq_inv] at hi
  simp_rw [quadratic_smul] at hi
  rw [integral_const_mul] at hi
  calc
    (∫ r in zonotope w, quadratic (principalForm w).adjugate r) =
        (principalForm w).det * ((principalForm w).det⁻¹ *
          (∫ r in zonotope w, quadratic (principalForm w).adjugate r)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hQ.det_pos.ne', one_mul]
    _ = (principalForm w).det * (64 * (principalForm w).det * moment (principalForm w)) := by rw [hi]
    _ = _ := by ring

end D4.Principal
