import D4.DelaunayFiniteSemantics
import D4.DelaunayPacking
import D4.BasisChange

noncomputable section
namespace D4.Delaunay
open Matrix Analytic Principal MeasureTheory

theorem simplexMatrix_cast (S : LatticeSimplex) :
    simplexMatrix (fun i => castVec (S i))=realMatrix (simplexMatrixZ S) := by
  ext i j
  simp [simplexMatrix,simplexMatrixZ,realMatrix,castVec]

theorem unimodular_simplex_volume (S : LatticeSimplex)
    (h : (simplexMatrixZ S).det=1 ∨ (simplexMatrixZ S).det = -1) :
    volume (simplexRegion S)=ENNReal.ofReal (1/24 : ℝ) := by
  have hd : |(simplexMatrix (fun i => castVec (S i))).det|=1 := by
    rw [simplexMatrix_cast,realMatrix_det]
    rcases h with h | h <;> simp [h]
  have hn : (simplexMatrix (fun i => castVec (S i))).det ≠ 0 := by
    intro h
    simp [h] at hd
  rw [simplexRegion,vertexSimplex_volume _ hn,hd]

theorem cells1_volume (s : Fin 24) : volume (simplexRegion (cells1 s))=ENNReal.ofReal (1/24 : ℝ) :=
  unimodular_simplex_volume _ (cells1_unimodular s)

theorem cells2_volume (s : Fin 24) : volume (simplexRegion (cells2 s))=ENNReal.ofReal (1/24 : ℝ) :=
  unimodular_simplex_volume _ (cells2_unimodular s)

theorem cells3_volume (s : Fin 24) : volume (simplexRegion (cells3 s))=ENNReal.ofReal (1/24 : ℝ) :=
  unimodular_simplex_volume _ (cells3_unimodular s)

theorem cells1_total_volume : (∑ s : Fin 24, volume (simplexRegion (cells1 s)))=1 := by
  simp only [cells1_volume,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num
  rw [show (24 : ENNReal)=ENNReal.ofReal (24:ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 24)]
  norm_num

theorem cells2_total_volume : (∑ s : Fin 24, volume (simplexRegion (cells2 s)))=1 := by
  simp only [cells2_volume,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num
  rw [show (24 : ENNReal)=ENNReal.ofReal (24:ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 24)]
  norm_num

theorem cells3_total_volume : (∑ s : Fin 24, volume (simplexRegion (cells3 s)))=1 := by
  simp only [cells3_volume,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num
  rw [show (24 : ENNReal)=ENNReal.ofReal (24:ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 24)]
  norm_num

end D4.Delaunay
