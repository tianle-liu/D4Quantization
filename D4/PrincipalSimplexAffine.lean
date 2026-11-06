import D4.PrincipalSimplexMoments
import D4.PrincipalTiles

/-! Affine change of variables for the actual four-simplex. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

def affineSimplex (B : Gram) (c : Vec) : Set Vec :=
  (fun x => c + B *ᵥ x) '' standardSimplex 4 1

theorem affineSimplex_compact (B : Gram) (c : Vec) : IsCompact (affineSimplex B c) :=
  (standardSimplex_compact 4 1).image (by unfold Matrix.mulVec dotProduct; fun_prop)

theorem affineSimplex_integral (B : Gram) (hB : B.det ≠ 0) (c : Vec) (f : Vec → ℝ) :
    (∫ y in affineSimplex B c, f y) =
      |B.det| * ∫ x in standardSimplex 4 1, f (c + B *ᵥ x) := by
  have h := setIntegral_map_equiv (μ := (volume : Measure Vec))
    (affineMeasurableEquiv B hB c) f (affineSimplex B c)
  change (∫ y in affineSimplex B c, f y ∂Measure.map (fun x => c + B *ᵥ x) volume) =
    (∫ x in (fun x => c + B *ᵥ x) ⁻¹' affineSimplex B c, f (c + B *ᵥ x)) at h
  have hp : (fun x => c + B *ᵥ x) ⁻¹' affineSimplex B c = standardSimplex 4 1 :=
    (affineMeasurableEquiv B hB c).injective.preimage_image (standardSimplex 4 1)
  rw [map_affine_volume B hB c, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)), smul_eq_mul, hp] at h
  calc
    (∫ y in affineSimplex B c, f y) =
        |B.det| * (|B.det|⁻¹ * (∫ y in affineSimplex B c, f y)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hB), one_mul]
    _ = _ := by rw [h]

theorem affineSimplex_volume (B : Gram) (hB : B.det ≠ 0) (c : Vec) :
    volume (affineSimplex B c) = ENNReal.ofReal (|B.det| / 24) := by
  have hi := affineSimplex_integral B hB c (fun _ => 1)
  rw [simplex4_one] at hi
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ] at hi
  rw [← ENNReal.ofReal_toReal (ne_of_lt (affineSimplex_compact B c).measure_lt_top), hi]
  congr 1
  ring

theorem simplex4_affine_quadratic {Q : Gram} (hQ : Q.IsHermitian)
    (B : Gram) (c : Vec) :
    (∫ x in standardSimplex 4 1, quadratic Q (c + B *ᵥ x)) =
      (30 * quadratic Q c + 12 * dotProduct c (Q *ᵥ (B *ᵥ 1)) +
        quadratic Q (B *ᵥ 1) + (B.transpose * Q * B).trace) / 720 := by
  have hc : IntegrableOn (fun _ : Vec => quadratic Q c) (standardSimplex 4 1) :=
    simplex4_integrable _ continuous_const
  have hl : IntegrableOn (fun x : Vec => 2 * dotProduct c (Q *ᵥ (B *ᵥ x)))
      (standardSimplex 4 1) :=
    simplex4_integrable _ (by unfold dotProduct Matrix.mulVec; fun_prop)
  have hq : IntegrableOn (fun x : Vec => quadratic Q (B *ᵥ x))
      (standardSimplex 4 1) :=
    simplex4_integrable _ ((quadratic_continuous Q).comp
      (Matrix.toLin' B).continuous_of_finiteDimensional)
  have hlinear : (∫ x in standardSimplex 4 1, 2 * dotProduct c (Q *ᵥ (B *ᵥ x))) =
      dotProduct c (Q *ᵥ (B *ᵥ 1)) / 60 := by
    simp_rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    rw [integral_const_mul, simplex4_linear]
    ring
  have hconstant : (∫ _x in standardSimplex 4 1, quadratic Q c) = quadratic Q c / 24 := by
    have hh := congrArg (fun t : ℝ => t * quadratic Q c) simplex4_one
    simpa only [integral_const, smul_eq_mul, mul_one, one_mul, div_eq_mul_inv, mul_comm] using hh
  simp_rw [quadratic_add_vec hQ]
  have hcl : IntegrableOn (fun x : Vec => quadratic Q c +
      2 * dotProduct c (Q *ᵥ (B *ᵥ x))) (standardSimplex 4 1) := hc.add hl
  rw [integral_add hcl hq, integral_add hc hl, hlinear, hconstant]
  simp_rw [← D4.quadratic_congruence Q B, simplex4_quadratic]
  ring

theorem affineSimplex_quadratic {Q : Gram} (hQ : Q.IsHermitian)
    (B : Gram) (hB : B.det ≠ 0) (c : Vec) :
    (∫ y in affineSimplex B c, quadratic Q y) =
      |B.det| / 720 * (30 * quadratic Q c + 12 * dotProduct c (Q *ᵥ (B *ᵥ 1)) +
        quadratic Q (B *ᵥ 1) + (B.transpose * Q * B).trace) := by
  rw [affineSimplex_integral B hB c, simplex4_affine_quadratic hQ]
  ring

end D4.Principal
