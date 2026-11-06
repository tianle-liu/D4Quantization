import D4.C23CellDefs

noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal

/-- Nonnegativity of every integer slack coefficient follows from the already
proved support of every generator; it need not be recomputed in finite tables. -/
theorem integerSlack_nonneg_of_support (g : Fin 9 → IntVec)
    (V : Fin 120 → Fin 10 → IntVec)
    (hSupport : ∀ w : Fin 10 → ℝ, (∀ j, 0 ≤ w j) → ∀ r,
      DualSupport (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ))
        (secondaryVertex V w r))
    (n : IntVec) (r : Fin 120) (k : Fin 10) : 0 ≤ integerSlack g V n r k := by
  classical
  let w : Fin 10 → ℝ := Pi.single k 1
  have hw : ∀ j, 0 ≤ w j := by intro j; simp only [w,Pi.single_apply]; split_ifs <;> norm_num
  have hh := hSupport w hw r n
  have he := facetSlack_secondaryVertex g V w n r
  have hv : 0 ≤ (facetSlack
      (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ)) n).eval
        (secondaryVertex V w r) := sub_nonneg.mpr hh
  rw [he] at hv
  have hh' : (0 : ℝ) ≤ (integerSlack g V n r k : ℝ) := by
    simpa [w,Pi.single_apply] using hv
  exact_mod_cast hh'

theorem c2_integerSlack_nonneg (n : IntVec) (r : Fin 120) (k : Fin 10) :
    0 ≤ integerSlack c2IntegerGenerators c2VertexCoefficients n r k := by
  apply integerSlack_nonneg_of_support
  intro w hw t
  exact secondaryVertex_support _ _ c2VertexAIndex c2_vertex_A c2_vertex_rankOne w hw t

theorem c3_integerSlack_nonneg (n : IntVec) (r : Fin 120) (k : Fin 10) :
    0 ≤ integerSlack c3IntegerGenerators c3VertexCoefficients n r k := by
  apply integerSlack_nonneg_of_support
  intro w hw t
  exact secondaryVertex_support _ _ c3VertexAIndex c3_vertex_A c3_vertex_rankOne w hw t

end D4.Secondary
