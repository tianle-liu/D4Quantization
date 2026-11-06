import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The displayed integer basis of D₄

This file proves the lattice identification in the final paragraph of the
article's Theorem 2.1. It does not assert a Voronoi moment formula or global
optimality. The integer image equality is proved by an explicit preimage,
so a determinant computation alone is not being used to infer surjectivity.
-/

namespace D4

open scoped Matrix

/-- The integer basis displayed in the paper, over an arbitrary coefficient ring. -/
def basisMatrix (R : Type*) [Ring R] : Matrix (Fin 4) (Fin 4) R :=
  !![1, 1, -1, -1;
     1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, -1]

/-- The matrix called `A` in the paper. -/
def gramMatrix (R : Type*) [Ring R] : Matrix (Fin 4) (Fin 4) R :=
  !![2, 1, -1, -1;
     1, 2, -1, -1;
     -1, -1, 2, 0;
     -1, -1, 0, 2]

abbrev basisMatrixZ := basisMatrix ℤ
abbrev gramMatrixZ := gramMatrix ℤ

/-- The Gram matrix identity is valid over every commutative ring. -/
theorem basisMatrix_transpose_mul (R : Type*) [CommRing R] :
    (basisMatrix R).transpose * basisMatrix R = gramMatrix R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, basisMatrix, gramMatrix]

/-- The determinant of the displayed basis is exactly two. -/
theorem det_basisMatrix (R : Type*) [CommRing R] :
    (basisMatrix R).det = 2 := by
  rw [Matrix.det_succ_row _ 1]
  norm_num [Fin.sum_univ_succ, basisMatrix]
  rw [Matrix.det_fin_three]
  change -(1 * 0 * (-1) - 1 * 0 * 1 - (-1) * 1 * (-1) +
    (-1) * 0 * 0 + (-1) * 1 * 1 - (-1) * 0 * 0 : R) = 2
  norm_num

/-- The determinant of the paper's matrix `A` is four. -/
theorem det_gramMatrix (R : Type*) [CommRing R] :
    (gramMatrix R).det = 4 := by
  rw [← basisMatrix_transpose_mul, Matrix.det_mul, Matrix.det_transpose,
    det_basisMatrix]
  norm_num

/-- The displayed Gram matrix is genuinely positive definite over the reals. -/
theorem gramMatrix_posDef : (gramMatrix ℝ).PosDef := by
  have hb : Function.Injective (basisMatrix ℝ).mulVec := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    rw [Matrix.isUnit_iff_isUnit_det, det_basisMatrix]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  have hi : (1 : Matrix (Fin 4) (Fin 4) ℝ).PosDef := Matrix.PosDef.one
  have h := hi.conjTranspose_mul_mul_same hb
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial,
    basisMatrix_transpose_mul] using h

/-- The inverse used in the trace normalization of the two nonprincipal cones. -/
noncomputable def inverseGramMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 1/2, 1/2;
     0, 1, 1/2, 1/2;
     1/2, 1/2, 1, 1/2;
     1/2, 1/2, 1/2, 1]

theorem inverseGramMatrix_mul : inverseGramMatrix * gramMatrix ℝ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, inverseGramMatrix, gramMatrix]

theorem gramMatrix_inv : (gramMatrix ℝ)⁻¹ = inverseGramMatrix :=
  Matrix.inv_eq_left_inv inverseGramMatrix_mul

/-- A rank-one generator, with its actual matrix interpretation. -/
def rankOne (v : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => v i * v j

/-- The nine rank-one vectors of cone C₂, in the article's order. -/
def cone2Vectors : Fin 9 → Fin 4 → ℝ :=
  ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1],
    ![1,0,-1,0], ![1,0,0,-1], ![0,1,-1,0], ![0,1,0,-1], ![0,0,1,-1]]

/-- Cone C₃ replaces the last C₂ rank-one vector by `(1,1,-1,-1)`. -/
def cone3Vectors : Fin 9 → Fin 4 → ℝ :=
  ![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1],
    ![1,0,-1,0], ![1,0,0,-1], ![0,1,-1,0], ![0,1,0,-1], ![1,1,-1,-1]]

theorem cone2_trace_normalization (j : Fin 9) :
    Matrix.trace ((gramMatrix ℝ)⁻¹ * rankOne (cone2Vectors j)) = 1 := by
  rw [gramMatrix_inv]
  fin_cases j <;>
    norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
      inverseGramMatrix, rankOne, cone2Vectors]

theorem cone3_trace_normalization (j : Fin 9) :
    Matrix.trace ((gramMatrix ℝ)⁻¹ * rankOne (cone3Vectors j)) = 1 := by
  rw [gramMatrix_inv]
  fin_cases j <;>
    norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
      inverseGramMatrix, rankOne, cone3Vectors]

/-- Coordinate expression for the lattice map defined by the displayed basis. -/
theorem basisMatrixZ_mulVec (n : Fin 4 → ℤ) :
    basisMatrixZ *ᵥ n =
      ![n 0 + n 1 - n 2 - n 3, n 0, n 1, n 2 - n 3] := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, basisMatrix] <;> ring

/-- The root lattice D₄ as integer vectors with even coordinate sum. -/
def evenSumLattice : Set (Fin 4 → ℤ) :=
  {z | (2 : ℤ) ∣ ∑ i, z i}

/-- Every column combination has even coordinate sum. -/
theorem basisMatrixZ_mulVec_mem (n : Fin 4 → ℤ) :
    basisMatrixZ *ᵥ n ∈ evenSumLattice := by
  change (2 : ℤ) ∣ ∑ i, (basisMatrixZ *ᵥ n) i
  refine ⟨n 0 + n 1 - n 3, ?_⟩
  rw [basisMatrixZ_mulVec]
  simp [Fin.sum_univ_succ]
  ring

/-- An explicit preimage of every integer vector with even coordinate sum. -/
theorem evenSumLattice_has_preimage (z : Fin 4 → ℤ) (hz : z ∈ evenSumLattice) :
    ∃ n : Fin 4 → ℤ, basisMatrixZ *ᵥ n = z := by
  obtain ⟨k, hk⟩ := hz
  simp [Fin.sum_univ_succ] at hk
  refine ⟨![z 1, z 2, k - z 0, k - z 0 - z 3], ?_⟩
  rw [basisMatrixZ_mulVec]
  ext i
  fin_cases i <;> simp
  omega

/-- The integer column span is exactly the root lattice D₄, not just a sublattice. -/
theorem range_basisMatrixZ_eq_evenSumLattice :
    Set.range (fun n : Fin 4 → ℤ => basisMatrixZ *ᵥ n) = evenSumLattice := by
  ext z
  constructor
  · rintro ⟨n, rfl⟩
    exact basisMatrixZ_mulVec_mem n
  · exact evenSumLattice_has_preimage z

end D4
