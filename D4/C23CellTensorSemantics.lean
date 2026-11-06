import D4.C23CellTensor
import D4.PrincipalTreeAlgebra

/-! Tensor contraction is the actual quadratic numerator of a five-vertex
simplex. These identities do not require matrix symmetry. -/
noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal

private theorem sum_rotate {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (f : ι → κ → ν → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem sum_cellVertices (V : Fin 120 → Vec) (c : SecondaryCell) :
    (∑ j : Fin 5, cellVertices V c j) = ∑ j : Fin 4, cellVector V c j := by
  ext i
  simp [Fin.sum_univ_succ, cellVertices, fanCellVertices, cellVector]

theorem sum_quadratic_cellVertices (A : Gram) (V : Fin 120 → Vec) (c : SecondaryCell) :
    (∑ j : Fin 5, quadratic A (cellVertices V c j)) =
      ∑ j : Fin 4, quadratic A (cellVector V c j) := by
  simp [Fin.sum_univ_succ, cellVertices, fanCellVertices, cellVector, quadratic]

theorem cellHessian_contraction (A : Gram) (V : Fin 120 → Vec) (c : SecondaryCell) :
    (∑ i, ∑ j, A i j * cellHessian V c i j) =
      quadratic A (∑ j : Fin 5, cellVertices V c j) +
        ∑ j : Fin 5, quadratic A (cellVertices V c j) := by
  rw [sum_cellVertices, sum_quadratic_cellVertices]
  simp only [cellHessian, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [quadratic_eq_sum]
    simp only [Finset.sum_apply]
  · simp only [Finset.mul_sum]
    rw [sum_rotate]
    apply Finset.sum_congr rfl
    intro k _
    rw [quadratic_eq_sum]

theorem cellTensor_contraction {τ : Type*} [Fintype τ] (A : Gram)
    (V : Fin 120 → Vec) (c : τ → SecondaryCell) (D : τ → ℝ) :
    (∑ i, ∑ j, A i j * ∑ t, D t * cellHessian V (c t) i j) =
      ∑ t, D t * (quadratic A (∑ j : Fin 5, cellVertices V (c t) j) +
        ∑ j : Fin 5, quadratic A (cellVertices V (c t) j)) := by
  simp only [Finset.mul_sum]
  rw [sum_rotate]
  apply Finset.sum_congr rfl
  intro t _
  rw [← cellHessian_contraction]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end D4.Secondary
