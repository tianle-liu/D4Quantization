import D4.C23CellDefs
import D4.PrincipalSimplexVertices

noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal

def supportRows (s : Fin 30 → AffineSlack) (c : SecondaryCell) (k : Fin 4) : Gram :=
  ![(s c.f).normal,(s c.g).normal,(s c.h).normal,Pi.single k 1]

theorem cell_matrix (V : Fin 120 → Vec) (c : SecondaryCell) :
    simplexMatrix (cellVertices V c) = fun i j => ![V c.p,V c.q,V c.u,V c.v] j i := by
  ext i j
  fin_cases j <;> simp [simplexMatrix,cellVertices,fanCellVertices]

theorem supportRows_mul_cellMatrix (s : Fin 30 → AffineSlack) (V : Fin 120 → Vec)
    (c : SecondaryCell) (k : Fin 4) (hc : FanCellGeometry s V c) :
    supportRows s c k * simplexMatrix (cellVertices V c) =
      !![(s c.f).offset,(s c.f).offset,(s c.f).offset,(s c.f).offset;
         dotProduct (s c.g).normal (V c.p),(s c.g).offset,(s c.g).offset,(s c.g).offset;
         dotProduct (s c.h).normal (V c.p),dotProduct (s c.h).normal (V c.q),
           (s c.h).offset,(s c.h).offset;
         V c.p k,V c.q k,V c.u k,V c.v k] := by
  rw [cell_matrix]
  have hfp := hc.f_p
  have hfq := hc.f_q
  have hfu := hc.f_u
  have hfv := hc.f_v
  have hgq := hc.g_q
  have hgu := hc.g_u
  have hgv := hc.g_v
  have hhu := hc.h_u
  have hhv := hc.h_v
  simp only [AffineSlack.eval, dotProduct] at hfp hfq hfu hfv hgq hgu hgv hhu hhv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [supportRows, Matrix.mul_apply, Pi.single_apply, dotProduct] <;>
    linarith

/-- A fan simplex determinant is a product of four linear factors. The
unimodular supporting rows will be checked as finite integer data. -/
theorem cell_determinant_factor (s : Fin 30 → AffineSlack) (V : Fin 120 → Vec)
    (c : SecondaryCell) (k : Fin 4) (hc : FanCellGeometry s V c) :
    (supportRows s c k).det * (simplexMatrix (cellVertices V c)).det =
      (s c.f).offset * (s c.g).eval (V c.p) * (s c.h).eval (V c.q) *
        (V c.v k - V c.u k) := by
  rw [← Matrix.det_mul,supportRows_mul_cellMatrix s V c k hc,Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, AffineSlack.eval]
  dsimp [Fin.succAbove, Fin.instOfNat, Fin.ofNat', Fin.lt_def, Fin.castSucc,
    Fin.succ, Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  norm_num
  ring

end D4.Secondary
