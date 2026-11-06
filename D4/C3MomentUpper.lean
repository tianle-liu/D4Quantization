import D4.C3CellMeasure
import D4.C23CellTensorSemantics
import D4.PrincipalTreeFiniteSemantics
set_option maxHeartbeats 0
noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal Certificate CertificateMoments

def c3RealTensor (w : Fin 10 → ℝ) : Gram := fun i j =>
  ∑ t, eval (extendWeight w) (c3CellDetPoly t) *
    cellHessian (secondaryVertex c3VertexCoefficients w) (c3Cell t) i j

theorem c3RealTensor_symmetric (w : Fin 10 → ℝ) (i j : Fin 4) :
    c3RealTensor w i j = c3RealTensor w j i := by
  unfold c3RealTensor
  apply Finset.sum_congr rfl
  intro t _
  rw [cellHessian_symm]

theorem c3_simplex_moment_upper (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    simplexMomentNumerator (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)) (c3CellVertices w) =
      upperContraction (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)).adjugate (c3RealTensor w) := by
  unfold simplexMomentNumerator
  simp only [c3_cell_abs_det w hw]
  change (∑ t, eval (extendWeight w) (c3CellDetPoly t) *
    (quadratic (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)).adjugate (∑ j,cellVertices (secondaryVertex c3VertexCoefficients w) (c3Cell t) j) +
      ∑ j,quadratic (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)).adjugate (cellVertices (secondaryVertex c3VertexCoefficients w) (c3Cell t) j))) = _
  rw [← cellTensor_contraction]
  apply symmetric_contraction_eq_upper
  · intro i j
    simpa only [star_trivial] using (secondary_isHermitian cone3Vectors (w 0) (fun j => w j.succ)).adjugate.apply j i
  · exact c3RealTensor_symmetric w

end D4.Secondary
