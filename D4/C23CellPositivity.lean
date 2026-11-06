import D4.C23CellTensor

/-! Positive cell determinants from supporting-face geometry and integer edge
coefficients. The signed edge and support determinant are checked separately;
no nondegeneracy of the actual simplex is assumed. -/
noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal Certificate

theorem linearPoly_pos (w : Fin 10 → ℝ) (a : Fin 10 → ℤ)
    (hw : ∀ j, 0 < w j) (ha : ∀ j, 0 ≤ a j) (hpos : ∃ j, 0 < a j) :
    0 < eval (extendWeight w) (linearPoly a) := by
  rw [linearPoly_eval]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hw j).le (by exact_mod_cast ha j)
  · obtain ⟨j,hj⟩ := hpos
    exact ⟨j,Finset.mem_univ _,mul_pos (hw j) (by exact_mod_cast hj)⟩

theorem cellFactorProduct_pos (g : Fin 9 → IntVec) (V : Fin 120 → Fin 10 → IntVec)
    (n : Fin 30 → IntVec) (w : Fin 10 → ℝ) (c : SecondaryCell) (k : Fin 4) (d : ℤ)
    (hw : ∀ j, 0 < w j)
    (hQ : (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)).PosDef)
    (hn : n c.f ≠ 0)
    (hc : FanCellGeometry
      (fun f => facetSlack (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)) (n f))
      (secondaryVertex V w) c)
    (he : ∀ j, 0 ≤ d * (V c.v j k - V c.u j k))
    (hep : ∃ j, 0 < d * (V c.v j k - V c.u j k)) :
    0 < eval (extendWeight w) (cellFactorProduct g V n c k d) := by
  have hn' : castVec (n c.f) ≠ 0 := by
    intro hz
    apply hn
    apply castVec_injective
    rw [hz]
    ext i
    simp [castVec]
  have hheight : 0 < quadratic
      (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)) (castVec (n c.f)) := by
    simpa [quadratic] using hQ.2 _ hn'
  simp only [cellFactorProduct,eval_mulMerge]
  change 0 < eval (extendWeight w) (linearPoly fun j => dotProduct (n c.f) (integerSecondaryGenerator g j *ᵥ n c.f)) *
      eval (extendWeight w) (linearPoly (integerSlack g V (n c.g) c.p)) *
      eval (extendWeight w) (linearPoly (integerSlack g V (n c.h) c.q)) *
      eval (extendWeight w) (linearPoly fun j => d * (V c.v j k - V c.u j k))
  rw [heightPoly_eval,linearPoly_eval,linearPoly_eval,
    ← facetSlack_secondaryVertex,← facetSlack_secondaryVertex]
  exact mul_pos (mul_pos (mul_pos hheight hc.g_p_pos) hc.h_q_pos)
    (linearPoly_pos w _ hw he hep)

theorem cell_simplex_det_pos (g : Fin 9 → IntVec) (V : Fin 120 → Fin 10 → IntVec)
    (n : Fin 30 → IntVec) (w : Fin 10 → ℝ) (c : SecondaryCell) (k : Fin 4) (d : ℤ)
    (hw : ∀ j, 0 < w j)
    (hQ : (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)).PosDef)
    (hn : n c.f ≠ 0) (hd : d^2 = 1) (hdet : (integerSupportRows n c k).det = d)
    (hc : FanCellGeometry
      (fun f => facetSlack (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)) (n f))
      (secondaryVertex V w) c)
    (he : ∀ j, 0 ≤ d * (V c.v j k - V c.u j k))
    (hep : ∃ j, 0 < d * (V c.v j k - V c.u j k)) :
    0 < (simplexMatrix (cellVertices (secondaryVertex V w) c)).det := by
  rw [← cellFactorProduct_eval g V n w c k d hd hdet hc]
  exact cellFactorProduct_pos g V n w c k d hw hQ hn hc he hep

theorem abs_cell_simplex_det_eq (g : Fin 9 → IntVec) (V : Fin 120 → Fin 10 → IntVec)
    (n : Fin 30 → IntVec) (w : Fin 10 → ℝ) (c : SecondaryCell) (k : Fin 4) (d : ℤ)
    (hw : ∀ j, 0 < w j)
    (hQ : (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)).PosDef)
    (hn : n c.f ≠ 0) (hd : d^2 = 1) (hdet : (integerSupportRows n c k).det = d)
    (hc : FanCellGeometry
      (fun f => facetSlack (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)) (n f))
      (secondaryVertex V w) c)
    (he : ∀ j, 0 ≤ d * (V c.v j k - V c.u j k))
    (hep : ∃ j, 0 < d * (V c.v j k - V c.u j k)) :
    |(simplexMatrix (cellVertices (secondaryVertex V w) c)).det| =
      eval (extendWeight w) (cellFactorProduct g V n c k d) := by
  rw [abs_of_pos (cell_simplex_det_pos g V n w c k d hw hQ hn hd hdet hc he hep)]
  exact (cellFactorProduct_eval g V n w c k d hd hdet hc).symm

theorem cellHessian_symm (V : Fin 120 → Vec) (c : SecondaryCell) (i j : Fin 4) :
    cellHessian V c i j = cellHessian V c j i := by
  simp only [cellHessian,mul_comm]

end D4.Secondary
