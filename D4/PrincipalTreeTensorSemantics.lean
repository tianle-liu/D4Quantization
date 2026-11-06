import D4.PrincipalTreeAlgebra

/-! Finite-sum algebra links the verified tensor contraction to the actual
quadratic integrals of the tree parallelotopes. -/
noncomputable section
namespace D4.Principal
open Matrix Analytic Certificate

private theorem sum_rotate {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (f : ι → κ → ν → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem treeHessian_contraction (w : Fin 10 → ℝ) (A : Gram) (t : Fin 125) :
    (∑ i, ∑ j, A i j * treeHessian w t i j) =
      3 * quadratic A (treeCenter w t) +
        ∑ k, w (treeEdges t k)^2 * quadratic A (cone1Vectors (treeEdges t k)) := by
  simp only [treeHessian, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [quadratic_eq_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp only [Finset.mul_sum]
    rw [sum_rotate]
    apply Finset.sum_congr rfl
    intro k _
    rw [quadratic_eq_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem treeTensor_contraction (w : Fin 10 → ℝ) (A : Gram) :
    (∑ i, ∑ j, A i j * treeTensor w i j) =
      ∑ t, treeWeight w t * (3 * quadratic A (treeCenter w t) +
        ∑ k, w (treeEdges t k)^2 * quadratic A (cone1Vectors (treeEdges t k))) := by
  simp only [treeTensor, Finset.mul_sum]
  rw [sum_rotate]
  apply Finset.sum_congr rfl
  intro t _
  rw [← treeHessian_contraction]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end D4.Principal
