import D4.PrincipalGeometry
import D4.BasisChange
import D4.EuclideanMoment
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Exact quadratic integrals on centered boxes and parallelotopes

These are Lebesgue integrals, established by the finite-product Fubini
theorem and the one-dimensional polynomial antiderivatives.
-/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

def centeredCube : Set Vec := Icc (-1) 1

theorem centeredCube_eq_pi :
    centeredCube = Set.univ.pi (fun _ : Fin 4 => Icc (-1 : ℝ) 1) := by
  ext x
  simp [centeredCube, Set.mem_Icc, Pi.le_def, forall_and]

theorem centeredCube_product (f : Fin 4 → ℝ → ℝ) :
    (∫ x in centeredCube, ∏ i, f i (x i)) =
      ∏ i, ∫ t in Icc (-1 : ℝ) 1, f i t := by
  rw [centeredCube_eq_pi, volume_pi, Measure.restrict_pi_pi]
  let μ : Measure ℝ := volume.restrict (Icc (-1 : ℝ) 1)
  change (∫ x : Vec, ∏ i, f i (x i) ∂Measure.pi (fun _ : Fin 4 => μ)) =
    ∏ i, ∫ t, f i t ∂μ
  letI : MeasureSpace ℝ := ⟨μ⟩
  haveI : SigmaFinite μ := by dsimp [μ]; infer_instance
  exact integral_fintype_prod_eq_prod (Fin 4) f

theorem centered_interval_one : (∫ t in Icc (-1 : ℝ) 1, (1 : ℝ)) = 2 := by
  norm_num

theorem centered_interval_id : (∫ t in Icc (-1 : ℝ) 1, t) = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  norm_num [integral_id]

theorem centered_interval_sq : (∫ t in Icc (-1 : ℝ) 1, t^2) = 2 / 3 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  norm_num [integral_pow]

theorem centeredCube_one : (∫ x in centeredCube, (1 : ℝ)) = 16 := by
  have h := centeredCube_product (fun _ _ => (1 : ℝ))
  norm_num [centered_interval_one] at h ⊢
  exact h

theorem centeredCube_coordinate (i : Fin 4) :
    (∫ x in centeredCube, x i) = 0 := by
  have h := centeredCube_product (fun k t => if k = i then t else 1)
  fin_cases i <;> simpa [Fin.prod_univ_four, centered_interval_id, centered_interval_one] using h

theorem centeredCube_coordinate_mul (i j : Fin 4) :
    (∫ x in centeredCube, x i * x j) = if i = j then (16 : ℝ) / 3 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    have h := centeredCube_product (fun k t => if k = i then t^2 else 1)
    have hi (k : Fin 4) :
        (∫ t in Icc (-1 : ℝ) 1, if k = i then t^2 else 1) =
          2 * (if k = i then (1 : ℝ)/3 else 1) := by
      by_cases hk : k = i
      · simp only [hk, ite_true, centered_interval_sq]
        ring
      · simp only [hk, ite_false, centered_interval_one]
        ring
    simp_rw [hi] at h
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite_eq',
      Finset.mem_univ, ite_true, Finset.card_univ, Fintype.card_fin] at h
    norm_num only at h
    simpa only [ite_true, pow_two] using h
  · have h := centeredCube_product (fun k t =>
      (if k = i then t else 1) * (if k = j then t else 1))
    have hp : (∏ k : Fin 4, ∫ t in Icc (-1 : ℝ) 1,
        (if k = i then t else 1) * (if k = j then t else 1)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simpa only [ite_true, hij, ite_false, mul_one] using centered_interval_id
    rw [hp] at h
    simpa only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
      ite_true, hij, ite_false] using h

theorem centeredCube_linear (v : Vec) :
    (∫ x in centeredCube, dotProduct v x) = 0 := by
  unfold dotProduct
  rw [integral_finset_sum]
  · simp [integral_const_mul, centeredCube_coordinate]
  · intro i _
    exact (show Continuous (fun x : Vec => v i * x i) by fun_prop).continuousOn.integrableOn_Icc

theorem quadratic_eq_sum (Q : Gram) (x : Vec) :
    quadratic Q x = ∑ i, ∑ j, Q i j * (x i * x j) := by
  simp only [quadratic, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem centeredCube_quadratic (Q : Gram) :
    (∫ x in centeredCube, quadratic Q x) = (16 : ℝ) / 3 * Q.trace := by
  simp_rw [quadratic_eq_sum]
  rw [integral_finset_sum]
  · have hi (i : Fin 4) :
        (∫ x in centeredCube, ∑ j, Q i j * (x i * x j)) =
          ∑ j, Q i j * (if i = j then (16 : ℝ) / 3 else 0) := by
      rw [integral_finset_sum]
      · simp only [integral_const_mul, centeredCube_coordinate_mul]
      · intro j _
        exact (show Continuous (fun x : Vec => Q i j * (x i * x j)) by
          fun_prop).continuousOn.integrableOn_Icc
    simp_rw [hi]
    simp [Matrix.trace, Finset.mul_sum, mul_ite, mul_comm]
  · intro i _
    exact (show Continuous (fun x : Vec => ∑ j, Q i j * (x i * x j)) by
      fun_prop).continuousOn.integrableOn_Icc

theorem quadratic_add_vec {Q : Gram} (hQ : Q.IsHermitian) (x y : Vec) :
    quadratic Q (x + y) = quadratic Q x +
      2 * dotProduct x (Q *ᵥ y) + quadratic Q y := by
  simp only [quadratic, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  rw [quadratic_pair_symmetric hQ y x]
  ring

theorem centeredCube_affine_quadratic {Q : Gram} (hQ : Q.IsHermitian)
    (B : Gram) (c : Vec) :
    (∫ x in centeredCube, quadratic Q (c + B *ᵥ x)) =
      16 * (quadratic Q c + (B.transpose * Q * B).trace / 3) := by
  have hc : IntegrableOn (fun _ : Vec => quadratic Q c) centeredCube := by
    exact continuous_const.continuousOn.integrableOn_Icc
  have hl : IntegrableOn (fun x : Vec => 2 * dotProduct c (Q *ᵥ (B *ᵥ x))) centeredCube := by
    exact (show Continuous (fun x : Vec => 2 * dotProduct c (Q *ᵥ (B *ᵥ x))) by
      unfold dotProduct Matrix.mulVec; fun_prop).continuousOn.integrableOn_Icc
  have hq : IntegrableOn (fun x : Vec => quadratic Q (B *ᵥ x)) centeredCube := by
    exact ((quadratic_continuous Q).comp (Matrix.toLin' B).continuous_of_finiteDimensional).continuousOn.integrableOn_Icc
  have hl0 : (∫ x in centeredCube, 2 * dotProduct c (Q *ᵥ (B *ᵥ x))) = 0 := by
    simp_rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    rw [integral_const_mul, centeredCube_linear, mul_zero]
  simp_rw [quadratic_add_vec hQ]
  have hcl : IntegrableOn (fun x : Vec => quadratic Q c + 2 * dotProduct c (Q *ᵥ (B *ᵥ x))) centeredCube := hc.add hl
  rw [integral_add hcl hq, integral_add hc hl, hl0]
  have hc0 : (∫ _x in centeredCube, quadratic Q c) = 16 * quadratic Q c := by
    have hh := centeredCube_one
    simpa only [integral_const, smul_eq_mul, mul_one] using congrArg (fun t : ℝ => t * quadratic Q c) hh
  rw [hc0]
  simp_rw [← D4.quadratic_congruence Q B, centeredCube_quadratic]
  ring

/-- The actual affine image of the centered cube. -/
def parallelotope (B : Gram) (c : Vec) : Set Vec :=
  (fun x => c + B *ᵥ x) '' centeredCube

def affineMeasurableEquiv (B : Gram) (hB : B.det ≠ 0) (c : Vec) : Vec ≃ᵐ Vec :=
  (Euclidean.coordinateEquiv B hB).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.trans
    (MeasurableEquiv.addLeft c)

@[simp] theorem affineMeasurableEquiv_apply (B : Gram) (hB : B.det ≠ 0) (c x : Vec) :
    affineMeasurableEquiv B hB c x = c + B *ᵥ x := rfl

theorem map_affine_volume (B : Gram) (hB : B.det ≠ 0) (c : Vec) :
    Measure.map (fun x => c + B *ᵥ x) volume =
      ENNReal.ofReal |B.det|⁻¹ • volume := by
  change Measure.map ((fun y : Vec => c + y) ∘ Matrix.toLin' B) volume = _
  have hm : Measurable (Matrix.toLin' B) :=
    (Euclidean.coordinateEquiv B hB).toContinuousLinearEquiv.continuous.measurable
  rw [← Measure.map_map (show Measurable (fun y : Vec => c + y) from measurable_const.add measurable_id) hm,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hB, Measure.map_smul,
    (measurePreserving_add_left (volume : Measure Vec) c).map_eq, abs_inv]

/-- Change of variables for an arbitrary integrand on a full dimensional
parallelotope. No unproved geometric decomposition enters this identity. -/
theorem parallelotope_integral (B : Gram) (hB : B.det ≠ 0) (c : Vec) (f : Vec → ℝ) :
    (∫ y in parallelotope B c, f y) =
      |B.det| * ∫ x in centeredCube, f (c + B *ᵥ x) := by
  have h := setIntegral_map_equiv (μ := (volume : Measure Vec))
    (affineMeasurableEquiv B hB c) f (parallelotope B c)
  change (∫ y in parallelotope B c, f y ∂Measure.map (fun x => c + B *ᵥ x) volume) =
    (∫ x in (fun x => c + B *ᵥ x) ⁻¹' parallelotope B c, f (c + B *ᵥ x)) at h
  have hp : (fun x => c + B *ᵥ x) ⁻¹' parallelotope B c = centeredCube :=
    (affineMeasurableEquiv B hB c).injective.preimage_image centeredCube
  rw [map_affine_volume B hB c, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)), smul_eq_mul, hp] at h
  calc
    (∫ y in parallelotope B c, f y) =
        |B.det| * (|B.det|⁻¹ * (∫ y in parallelotope B c, f y)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hB), one_mul]
    _ = _ := by rw [h]

/-- The exact local integration formula used for each tree tile in the paper. -/
theorem parallelotope_quadratic {Q : Gram} (hQ : Q.IsHermitian)
    (B : Gram) (hB : B.det ≠ 0) (c : Vec) :
    (∫ y in parallelotope B c, quadratic Q y) =
      16 * |B.det| * (quadratic Q c + (B.transpose * Q * B).trace / 3) := by
  rw [parallelotope_integral B hB c, centeredCube_affine_quadratic hQ]
  ring

end D4.Principal
