import D4.C2CellMeasure
import D4.C23CellTensorSemantics
import D4.PrincipalTreeFiniteSemantics
set_option maxHeartbeats 0
noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal Certificate CertificateMoments

def c2RealTensor (w : Fin 10 → ℝ) : Gram := fun i j =>
  ∑ t, eval (extendWeight w) (c2CellDetPoly t) *
    cellHessian (secondaryVertex c2VertexCoefficients w) (c2Cell t) i j

theorem c2RealTensor_symmetric (w : Fin 10 → ℝ) (i j : Fin 4) :
    c2RealTensor w i j = c2RealTensor w j i := by
  unfold c2RealTensor
  apply Finset.sum_congr rfl
  intro t _
  rw [cellHessian_symm]

theorem c2_simplex_moment_upper (w : Fin 10 → ℝ) (hw : ∀ k, 0 < w k) :
    simplexMomentNumerator (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)) (c2CellVertices w) =
      upperContraction (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate (c2RealTensor w) := by
  unfold simplexMomentNumerator
  simp only [c2_cell_abs_det w hw]
  change (∑ t, eval (extendWeight w) (c2CellDetPoly t) *
    (quadratic (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate (∑ j,cellVertices (secondaryVertex c2VertexCoefficients w) (c2Cell t) j) +
      ∑ j,quadratic (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).adjugate (cellVertices (secondaryVertex c2VertexCoefficients w) (c2Cell t) j))) = _
  rw [← cellTensor_contraction]
  apply symmetric_contraction_eq_upper
  · intro i j
    simpa only [star_trivial] using (secondary_isHermitian cone2Vectors (w 0) (fun j => w j.succ)).adjugate.apply j i
  · exact c2RealTensor_symmetric w

end D4.Secondary
