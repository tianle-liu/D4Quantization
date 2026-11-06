import D4.Targets
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The topology for secondary domains is the relative topology of symmetric
 matrices, not the ambient sixteen-dimensional space of arbitrary matrices. -/
noncomputable section
namespace D4.Delaunay
open Matrix Analytic

abbrev SymGram := {Q : Gram // Q.IsSymm}

def symmetricCongruence (R : Gram) (Q : SymGram) : SymGram :=
  ⟨Rᵀ * Q.1 * R, by
    change (Rᵀ * Q.1 * R)ᵀ=Rᵀ * Q.1 * R
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Q.2.eq]
    simp only [Matrix.mul_assoc]⟩

theorem symmetricCongruence_continuous (R : Gram) : Continuous (symmetricCongruence R) := by
  apply Continuous.subtype_mk
  change Continuous (fun Q : SymGram => Rᵀ * Q.1 * R)
  fun_prop

theorem symmetricCongruence_comp (R T : Gram) (Q : SymGram) :
    symmetricCongruence R (symmetricCongruence T Q)=symmetricCongruence (T*R) Q := by
  apply Subtype.ext
  change Rᵀ * (Tᵀ * Q.1 * T) * R=(T*R)ᵀ * Q.1 * (T*R)
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

@[simp] theorem symmetricCongruence_one (Q : SymGram) : symmetricCongruence 1 Q=Q := by
  apply Subtype.ext
  simp only [symmetricCongruence, transpose_one, one_mul, mul_one]

/-- The change-of-basis action is a homeomorphism of the symmetric space. -/
def symmetricCongruenceHomeomorph (R : Gram) (hR : IsUnit R.det) : SymGram ≃ₜ SymGram where
  toFun := symmetricCongruence R
  invFun := symmetricCongruence R⁻¹
  left_inv := by
    intro Q
    rw [symmetricCongruence_comp, Matrix.mul_nonsing_inv _ hR, symmetricCongruence_one]
  right_inv := by
    intro Q
    rw [symmetricCongruence_comp, Matrix.nonsing_inv_mul _ hR, symmetricCongruence_one]
  continuous_toFun := symmetricCongruence_continuous R
  continuous_invFun := symmetricCongruence_continuous R⁻¹

end D4.Delaunay
