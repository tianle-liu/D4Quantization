import D4.ParityNearest
import D4.PrincipalGeometry

/-! Integer support inequalities for the 24-cell and for rank-one summands.
The competitors range over the entire integer lattice. -/
noncomputable section
namespace D4.Secondary
open Matrix Analytic Quantizer

/-- Dual Voronoi membership, stated as all integer support inequalities. -/
def DualSupport (Q : Gram) (r : Vec) : Prop :=
  ∀ z : IntVec, dotProduct (castVec z) r ≤ quadratic Q (castVec z)

theorem squaredError_expand (p : Vec) (z : IntVec) :
    squaredError p z = dotProduct p p - 2 * dotProduct p (castVec z) +
      dotProduct (castVec z) (castVec z) := by
  simp only [squaredError, dotProduct, castVec, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gram_support_of_minimum (p : Vec)
    (hmin : ∀ z : IntVec, z ∈ evenSumLattice → squaredError p 0 ≤ squaredError p z) :
    DualSupport (gramMatrix ℝ) ((2 : ℝ) • ((basisMatrix ℝ).transpose *ᵥ p)) := by
  intro z
  have h := hmin (basisMatrixZ *ᵥ z) (basisMatrixZ_mulVec_mem z)
  rw [squaredError_expand, squaredError_expand, cast_basis_mulVec] at h
  have hz : castVec (0 : IntVec) = (0 : Vec) := by ext i; simp [castVec]
  rw [hz, dotProduct_zero, dotProduct_zero, mul_zero, sub_zero, add_zero] at h
  have hq : quadratic (gramMatrix ℝ) (castVec z) =
      dotProduct (basisMatrix ℝ *ᵥ castVec z) (basisMatrix ℝ *ᵥ castVec z) := by
    rw [← basisMatrix_transpose_mul]
    simp only [quadratic, ← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  rw [hq, dotProduct_smul, smul_eq_mul, dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  linarith

theorem physical_half_minimum (p : Vec) (hp : ∀ i, |p i| ≤ 1/2)
    (z : IntVec) : squaredError p 0 ≤ squaredError p z := by
  apply Finset.sum_le_sum
  intro i _
  simpa only [Pi.zero_apply, Int.cast_zero, sub_zero] using
    sub_nonneg.mp (scalar_integer_minimum (hp i) (z i))

theorem physical_odd_minimum (p : IntVec) (hp : p ∉ evenSumLattice)
    (hpn : squaredError (castVec p) 0 = 1) (z : IntVec) (hz : z ∈ evenSumLattice) :
    squaredError (castVec p) 0 ≤ squaredError (castVec p) z := by
  have hzp : z-p ≠ 0 := by
    intro he
    exact hp (sub_eq_zero.mp he ▸ hz)
  have hc : (0 : Vec) ∈ centeredCube := by simp [centeredCube]
  have h := squaredError_nonzero_gap hc hzp
  have he : squaredError (0 : Vec) (z-p) = squaredError (castVec p) z := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.zero_apply, Pi.sub_apply, Int.cast_sub, castVec]
    ring
  rw [he] at h
  rw [hpn]
  simpa [squaredError] using h

theorem rankOne_support (v : IntVec) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    DualSupport (rankOne (castVec v)) ((s : ℝ) • castVec v) := by
  intro z
  rw [Principal.quadratic_rankOne, dotProduct_smul, smul_eq_mul]
  have hi : dotProduct (castVec z) (castVec v) = ((dotProduct z v : ℤ) : ℝ) := by
    simp [dotProduct, castVec]
  rw [hi]
  have h := Principal.abs_intCast_le_sq (dotProduct z v)
  rcases hs with rfl | rfl <;> norm_num at ⊢ <;>
    linarith [le_abs_self ((dotProduct z v : ℤ) : ℝ), neg_le_abs ((dotProduct z v : ℤ) : ℝ)]

end D4.Secondary
