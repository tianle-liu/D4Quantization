import D4.Targets
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Ring.Int.Units

/-!
# Unimodular changes of coordinates for the genuine nearest-point function

The integer and real coordinate maps are actual linear equivalences. The
nearest-point identity reindexes the entire integer lattice through that
bijection; no finite approximation or moment formula is used.
-/
noncomputable section
namespace D4
open Matrix Analytic

/-- Casting the determinant commutes with the actual integer matrix map. -/
theorem realMatrix_det (U : IntegerMatrix) : (realMatrix U).det = (U.det : ℝ) :=
  ((Int.castRingHom ℝ).map_det U).symm

theorem realMatrix_det_isUnit (U : IntegerMatrix) (hU : IsUnit U.det) :
    IsUnit (realMatrix U).det := by
  rw [realMatrix_det]
  exact hU.map (Int.castRingHom ℝ)

/-- The integral coordinate change and its integral inverse. -/
noncomputable def integerBasisEquiv (U : IntegerMatrix) (hU : IsUnit U.det) :
    IntVec ≃ₗ[ℤ] IntVec :=
  { U.mulVecLin with
    invFun := U⁻¹.mulVec
    left_inv := fun z => by
      change U⁻¹ *ᵥ (U *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU,
        Matrix.one_mulVec]
    right_inv := fun z => by
      change U *ᵥ (U⁻¹ *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU,
        Matrix.one_mulVec] }

@[simp] theorem integerBasisEquiv_apply (U : IntegerMatrix) (hU : IsUnit U.det) (z : IntVec) :
    integerBasisEquiv U hU z = U *ᵥ z := rfl

@[simp] theorem integerBasisEquiv_symm_apply (U : IntegerMatrix) (hU : IsUnit U.det) (z : IntVec) :
    (integerBasisEquiv U hU).symm z = U⁻¹ *ᵥ z := rfl

/-- The corresponding real linear equivalence, with the same forward matrix. -/
noncomputable def realBasisEquiv (U : IntegerMatrix) (hU : IsUnit U.det) : Vec ≃ₗ[ℝ] Vec :=
  { (realMatrix U).mulVecLin with
    invFun := (realMatrix U)⁻¹.mulVec
    left_inv := fun x => by
      change (realMatrix U)⁻¹ *ᵥ (realMatrix U *ᵥ x) = x
      rw [Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (realMatrix_det_isUnit U hU), Matrix.one_mulVec]
    right_inv := fun x => by
      change realMatrix U *ᵥ ((realMatrix U)⁻¹ *ᵥ x) = x
      rw [Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (realMatrix_det_isUnit U hU), Matrix.one_mulVec] }

@[simp] theorem realBasisEquiv_apply (U : IntegerMatrix) (hU : IsUnit U.det) (x : Vec) :
    realBasisEquiv U hU x = realMatrix U *ᵥ x := rfl

@[simp] theorem realBasisEquiv_symm_apply (U : IntegerMatrix) (hU : IsUnit U.det) (x : Vec) :
    (realBasisEquiv U hU).symm x = (realMatrix U)⁻¹ *ᵥ x := rfl

/-- The image of integer lattice points agrees with casting the integer map. -/
theorem castVec_mulVec (U : IntegerMatrix) (z : IntVec) :
    castVec (U *ᵥ z) = realMatrix U *ᵥ castVec z := by
  ext i
  simp [castVec, realMatrix, Matrix.mulVec, dotProduct]

theorem realBasisEquiv_castVec (U : IntegerMatrix) (hU : IsUnit U.det) (z : IntVec) :
    realBasisEquiv U hU (castVec z) = castVec (integerBasisEquiv U hU z) :=
  (castVec_mulVec U z).symm

/-- Equivariance for the integer-translation action on the real coordinate space. -/
theorem realBasisEquiv_integer_translate (U : IntegerMatrix) (hU : IsUnit U.det)
    (z : IntVec) (x : Vec) :
    realBasisEquiv U hU (castVec z + x) =
      castVec (integerBasisEquiv U hU z) + realBasisEquiv U hU x := by
  rw [map_add, realBasisEquiv_castVec]

/-- The linear-map determinant used by Lebesgue change of variables. -/
theorem realBasisEquiv_det (U : IntegerMatrix) (hU : IsUnit U.det) :
    LinearMap.det (realBasisEquiv U hU).toLinearMap = (realMatrix U).det :=
  LinearMap.det_toLin' (realMatrix U)

theorem integer_mulVec_bijective (U : IntegerMatrix) (hU : IsUnit U.det) :
    Function.Bijective (fun z : IntVec => U *ᵥ z) :=
  (integerBasisEquiv U hU).bijective

/-- Quadratic forms transform by congruence for every real coordinate matrix. -/
theorem quadratic_congruence (Q R : RealGram) (x : Vec) :
    quadratic (R.transpose * Q * R) x = quadratic Q (R *ᵥ x) := by
  unfold quadratic
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Reindexing all integer vectors proves the exact nearest-point identity. -/
theorem nearest_unimodular (Q : RealGram) (U : IntegerMatrix) (hU : IsUnit U.det) (x : Vec) :
    nearest ((realMatrix U).transpose * Q * realMatrix U) x =
      nearest Q (realMatrix U *ᵥ x) := by
  unfold nearest
  apply (integerBasisEquiv U hU).toEquiv.iInf_congr
  intro z
  rw [quadratic_congruence, Matrix.mulVec_sub]
  simp only [LinearEquiv.coe_toEquiv, integerBasisEquiv_apply, castVec_mulVec]

/-- A unimodular integer matrix has real determinant of absolute value one. -/
theorem abs_det_realMatrix (U : IntegerMatrix) (hU : IsUnit U.det) :
    |(realMatrix U).det| = 1 := by
  rw [realMatrix_det]
  rcases Int.isUnit_iff.mp hU with h | h <;> rw [h] <;> norm_num

theorem sq_det_realMatrix (U : IntegerMatrix) (hU : IsUnit U.det) :
    (realMatrix U).det ^ 2 = 1 := by
  rw [realMatrix_det]
  rcases Int.isUnit_iff.mp hU with h | h <;> rw [h] <;> norm_num

/-- The Gram determinant is unchanged by an integral basis change. -/
theorem det_unimodular_congruence (Q : RealGram) (U : IntegerMatrix) (hU : IsUnit U.det) :
    ((realMatrix U).transpose * Q * realMatrix U).det = Q.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  calc
    _ = ((realMatrix U).det ^ 2) * Q.det := by ring
    _ = Q.det := by rw [sq_det_realMatrix U hU, one_mul]

/-- Positive definiteness is preserved by the actual real coordinate equivalence. -/
theorem posDef_unimodular_congruence {Q : RealGram} (hQ : Q.PosDef)
    (U : IntegerMatrix) (hU : IsUnit U.det) :
    ((realMatrix U).transpose * Q * realMatrix U).PosDef := by
  have h := hQ.conjTranspose_mul_mul_same (realBasisEquiv U hU).injective
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

end D4
