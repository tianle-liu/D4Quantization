import D4.ParityMoment
import D4.EuclideanMoment

/-! The scalar-quantizer comparison uses the actual Euclidean integer
lattice and its actual Voronoi integral. -/
noncomputable section
namespace D4.Quantizer
open Analytic Matrix MeasureTheory Set

theorem quadratic_one_sub_eq_squaredError (x : Vec) (z : IntVec) :
    quadratic (1 : Gram) (x-castVec z) = squaredError x z := by
  simp only [quadratic, Matrix.one_mulVec, dotProduct, squaredError, Pi.sub_apply, castVec]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem quadratic_one_eq_squaredError (x : Vec) :
    quadratic (1 : Gram) x = squaredError x 0 := by
  simp only [quadratic, Matrix.one_mulVec, dotProduct, squaredError,
    Pi.zero_apply, Int.cast_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem voronoi_one_eq_centeredCube : voronoi (1 : Gram) = centeredCube := by
  ext x
  constructor
  · intro hx
    rw [centeredCube_eq_Icc]
    constructor <;> intro i
    · have H := hx (Pi.single i (-1))
      rw [quadratic_one_eq_squaredError, quadratic_one_sub_eq_squaredError,
        squaredError_single] at H
      norm_num at H
      linarith
    · have H := hx (Pi.single i 1)
      rw [quadratic_one_eq_squaredError, quadratic_one_sub_eq_squaredError,
        squaredError_single] at H
      norm_num at H
      linarith
  · intro hx z
    rw [quadratic_one_eq_squaredError, quadratic_one_sub_eq_squaredError]
    exact squaredError_minimum hx z

theorem moment_one : moment (1 : Gram) = 1/3 := by
  rw [moment_eq_voronoi Matrix.PosDef.one, voronoi_one_eq_centeredCube]
  simp_rw [quadratic_one_eq_squaredError]
  exact integral_squaredError_centeredCube

theorem normalizedMoment_one : normalizedMoment (1 : Gram) = 1/12 := by
  simp [normalizedMoment, moment_one]
  norm_num

theorem euclidean_integer_lattice_normalizedMoment :
    Euclidean.normalizedCellMoment (1 : Gram) = 1/12 := by
  rw [Euclidean.normalizedCellMoment_eq (by simp)]
  simpa [Euclidean.gram] using normalizedMoment_one

theorem euclidean_d4_normalizedMoment :
    Euclidean.normalizedCellMoment (D4.basisMatrix ℝ) = optimalConstant := by
  rw [Euclidean.normalizedCellMoment_eq (by rw [D4.det_basisMatrix]; norm_num)]
  simpa only [Euclidean.gram, D4.basisMatrix_transpose_mul] using normalizedMoment_gramMatrix

theorem d4_scalar_distortion_ratio :
    Euclidean.normalizedCellMoment (D4.basisMatrix ℝ) /
      Euclidean.normalizedCellMoment (1 : Gram) = 13/(10*Real.sqrt 2) := by
  rw [euclidean_d4_normalizedMoment, euclidean_integer_lattice_normalizedMoment]
  unfold optimalConstant
  ring

end D4.Quantizer
