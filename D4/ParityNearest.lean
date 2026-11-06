import D4.ParityQuantizer
import D4.EuclideanMoment
import D4.BasisChange

/-! The parity algorithm computes the actual infinite-lattice infimum. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Quantizer
open Analytic

def basisEquiv : Vec ≃ₗ[ℝ] Vec :=
  Euclidean.coordinateEquiv (basisMatrix ℝ) (by rw [det_basisMatrix]; norm_num)

@[simp] theorem basisEquiv_apply (x : Vec) : basisEquiv x = basisMatrix ℝ *ᵥ x := rfl

theorem cast_basis_mulVec (z : IntVec) :
    castVec (basisMatrixZ *ᵥ z) = basisMatrix ℝ *ᵥ castVec z := by
  have h := castVec_mulVec basisMatrixZ z
  have he : realMatrix basisMatrixZ = basisMatrix ℝ := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [realMatrix, basisMatrix]
  rwa [he] at h

def physicalNearest (x : Vec) : ℝ := nearest (gramMatrix ℝ) (basisEquiv.symm x)

theorem gram_error_eq (x : Vec) (z : IntVec) :
    quadratic (gramMatrix ℝ) (basisEquiv.symm x - castVec z) =
      squaredError x (basisMatrixZ *ᵥ z) := by
  rw [← basisMatrix_transpose_mul ℝ]
  have he : (basisMatrix ℝ).transpose * basisMatrix ℝ =
      (basisMatrix ℝ).transpose * (1 : Gram) * basisMatrix ℝ := by simp
  rw [he, quadratic_congruence, Matrix.mulVec_sub,
    ← basisEquiv_apply, basisEquiv.apply_symm_apply, ← cast_basis_mulVec]
  simp [quadratic, squaredError, dotProduct, castVec, pow_two]

theorem physicalNearest_le (x : Vec) {z : IntVec} (hz : z ∈ evenSumLattice) :
    physicalNearest x ≤ squaredError x z := by
  obtain ⟨n, rfl⟩ := evenSumLattice_has_preimage z hz
  simpa only [physicalNearest, gram_error_eq] using
    nearest_le gramMatrix_posDef.posSemidef (basisEquiv.symm x) n

theorem physicalNearest_eq_minimum (x : Vec) {z : IntVec} (hz : z ∈ evenSumLattice)
    (hmin : ∀ w ∈ evenSumLattice, squaredError x z ≤ squaredError x w) :
    physicalNearest x = squaredError x z := by
  refine le_antisymm (physicalNearest_le x hz) ?_
  apply le_ciInf
  intro n
  rw [gram_error_eq]
  exact hmin _ (basisMatrixZ_mulVec_mem n)

theorem physicalNearest_centeredCube {x : Vec} (hx : x ∈ centeredCube) :
    physicalNearest x = squaredError x 0 :=
  physicalNearest_eq_minimum x (by simp [evenSumLattice])
    (fun w _ => squaredError_minimum hx w)

def oddUnit : IntVec := Pi.single 0 1

theorem oddUnit_not_even : oddUnit ∉ evenSumLattice := by
  norm_num [oddUnit, evenSumLattice]

theorem even_add_oddUnit_iff (z : IntVec) :
    z + oddUnit ∈ evenSumLattice ↔ z ∉ evenSumLattice := by
  simp only [evenSumLattice, Set.mem_setOf_eq, Pi.add_apply, Finset.sum_add_distrib]
  have he : ∑ i, oddUnit i = 1 := by simp [oddUnit]
  rw [he]
  omega

theorem odd_sub_oddUnit_of_even {z : IntVec} (hz : z ∈ evenSumLattice) :
    z - oddUnit ∉ evenSumLattice := by
  have h := (even_add_oddUnit_iff (z-oddUnit)).mp
  apply h
  simpa only [sub_add_cancel] using hz

theorem squaredError_translate (x : Vec) (z k : IntVec) :
    squaredError (x + castVec k) z = squaredError x (z-k) := by
  unfold squaredError
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.add_apply, Pi.sub_apply, castVec, Int.cast_sub]
  ring

theorem physicalNearest_oddCube {x : Vec} (hx : x ∈ centeredCube) :
    physicalNearest (x + castVec oddUnit) = squaredError x 0 + 1 - 2*‖x‖ := by
  obtain ⟨z, hz, he, hmin⟩ := exists_odd_correction hx
  have hp := physicalNearest_eq_minimum (x + castVec oddUnit)
    ((even_add_oddUnit_iff z).mpr hz) (fun w hw => by
      simp only [squaredError_translate, add_sub_cancel_right]
      exact hmin _ (odd_sub_oddUnit_of_even hw))
  simpa only [squaredError_translate, add_sub_cancel_right, he] using hp

end D4.Quantizer
