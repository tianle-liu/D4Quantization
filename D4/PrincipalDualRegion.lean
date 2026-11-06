import D4.PrincipalMomentTransform
import D4.VoronoiCompact

/-! The genuine dual Voronoi region for an arbitrary positive definite
Gram matrix. Its defining inequalities range over every integer site. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

def dualRegion (Q : Gram) : Set Vec :=
  {r | ∀ z : IntVec, dotProduct (castVec z) r ≤ quadratic Q (castVec z)}

theorem dualRegion_convex (Q : Gram) : Convex ℝ (dualRegion Q) := by
  intro x hx y hy a b ha hb hab z
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  calc
    _ ≤ a * quadratic Q (castVec z) + b * quadratic Q (castVec z) :=
      add_le_add (mul_le_mul_of_nonneg_left (hx z) ha) (mul_le_mul_of_nonneg_left (hy z) hb)
    _ = _ := by rw [← add_mul, hab, one_mul]

theorem dualRegion_preimage {Q : Gram} (hQ : Q.IsHermitian) :
    (fun x : Vec => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) ⁻¹' dualRegion Q = voronoi Q := by
  ext x
  change (∀ z : IntVec, dotProduct (castVec z) (0 + ((2 : ℝ) • Q) *ᵥ x) ≤
    quadratic Q (castVec z)) ↔ ∀ z : IntVec, quadratic Q x ≤ quadratic Q (x - castVec z)
  simp only [zero_add, Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
  simp_rw [quadratic_pair_symmetric hQ (castVec _) x, quadratic_sub_vec hQ]
  constructor <;> intro h z <;> have hz := h z <;> linarith

theorem dualRegion_det (Q : Gram) : ((2 : ℝ) • Q).det = 16 * Q.det := by
  rw [Matrix.det_smul]
  norm_num

theorem dualRegion_det_pos {Q : Gram} (hQ : Q.PosDef) : 0 < ((2 : ℝ) • Q).det := by
  rw [dualRegion_det]
  exact mul_pos (by norm_num) hQ.det_pos

theorem dualRegion_image {Q : Gram} (hQ : Q.PosDef) :
    dualRegion Q = (fun x : Vec => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) '' voronoi Q := by
  have h := Set.image_preimage_eq (dualRegion Q)
    (affineMeasurableEquiv ((2 : ℝ) • Q) (dualRegion_det_pos hQ).ne' 0).surjective
  change (fun x : Vec => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) ''
    ((fun x : Vec => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) ⁻¹' dualRegion Q) = dualRegion Q at h
  rw [dualRegion_preimage hQ.isHermitian] at h
  exact h.symm

theorem dualRegion_compact {Q : Gram} (hQ : Q.PosDef) : IsCompact (dualRegion Q) := by
  rw [dualRegion_image hQ]
  exact (voronoi_compact hQ).image
    (continuous_const.add (Matrix.toLin' ((2 : ℝ) • Q)).continuous_of_finiteDimensional)

theorem dualRegion_volume {Q : Gram} (hQ : Q.PosDef) :
    volume (dualRegion Q) = ENNReal.ofReal (16 * Q.det) := by
  have hB : ((2 : ℝ) • Q).det ≠ 0 := (dualRegion_det_pos hQ).ne'
  have hm : Measurable (fun x : Vec => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) :=
    (affineMeasurableEquiv ((2 : ℝ) • Q) hB 0).measurable
  have h := congrArg (fun μ : Measure Vec => μ (dualRegion Q)) (map_affine_volume ((2 : ℝ) • Q) hB 0)
  change (Measure.map (fun x : Vec => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) volume) (dualRegion Q) =
    (ENNReal.ofReal |((2 : ℝ) • Q).det|⁻¹ • volume) (dualRegion Q) at h
  rw [Measure.map_apply hm (dualRegion_compact hQ).measurableSet,
    dualRegion_preimage hQ.isHermitian, voronoi_volume hQ] at h
  simp only [Measure.smul_apply, smul_eq_mul] at h
  rw [abs_of_pos (dualRegion_det_pos hQ), ENNReal.ofReal_inv_of_pos (dualRegion_det_pos hQ)] at h
  have hn : ENNReal.ofReal ((2 : ℝ) • Q).det ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (dualRegion_det_pos hQ))
  calc
    volume (dualRegion Q) = ENNReal.ofReal ((2 : ℝ) • Q).det *
        ((ENNReal.ofReal ((2 : ℝ) • Q).det)⁻¹ * volume (dualRegion Q)) :=
      (ENNReal.mul_inv_cancel_left hn ENNReal.ofReal_ne_top).symm
    _ = ENNReal.ofReal ((2 : ℝ) • Q).det := by rw [← h, mul_one]
    _ = _ := by rw [dualRegion_det]

theorem dualRegion_inverse_moment {Q : Gram} (hQ : Q.PosDef) :
    (∫ r in dualRegion Q, quadratic Q⁻¹ r) = 64 * Q.det * moment Q := by
  have hB : ((2 : ℝ) • Q).det ≠ 0 := (dualRegion_det_pos hQ).ne'
  have h := setIntegral_map_equiv (μ := (volume : Measure Vec))
    (affineMeasurableEquiv ((2 : ℝ) • Q) hB 0) (quadratic Q⁻¹) (dualRegion Q)
  change (∫ r in dualRegion Q, quadratic Q⁻¹ r ∂Measure.map (fun x => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) volume) =
    (∫ x in (fun x => (0 : Vec) + ((2 : ℝ) • Q) *ᵥ x) ⁻¹' dualRegion Q,
      quadratic Q⁻¹ (0 + ((2 : ℝ) • Q) *ᵥ x)) at h
  rw [map_affine_volume ((2 : ℝ) • Q) hB 0, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)), smul_eq_mul,
    abs_of_pos (dualRegion_det_pos hQ), dualRegion_preimage hQ.isHermitian] at h
  simp_rw [zero_add, quadratic_inverse_dual hQ] at h
  rw [integral_const_mul, ← moment_eq_voronoi hQ, dualRegion_det] at h
  calc
    (∫ r in dualRegion Q, quadratic Q⁻¹ r) =
        (16 * Q.det) * ((16 * Q.det)⁻¹ * (∫ r in dualRegion Q, quadratic Q⁻¹ r)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (by norm_num) hQ.det_pos.ne'), one_mul]
    _ = (16 * Q.det) * (4 * moment Q) := by rw [h]
    _ = _ := by ring

theorem dualRegion_adjugate_moment {Q : Gram} (hQ : Q.PosDef) :
    (∫ r in dualRegion Q, quadratic Q.adjugate r) = 64 * Q.det^2 * moment Q := by
  have hi := dualRegion_inverse_moment hQ
  rw [Matrix.inv_def, Ring.inverse_eq_inv] at hi
  simp_rw [quadratic_smul] at hi
  rw [integral_const_mul] at hi
  calc
    (∫ r in dualRegion Q, quadratic Q.adjugate r) = Q.det * (Q.det⁻¹ *
        (∫ r in dualRegion Q, quadratic Q.adjugate r)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hQ.det_pos.ne', one_mul]
    _ = Q.det * (64 * Q.det * moment Q) := by rw [hi]
    _ = _ := by ring

end D4.Principal
