import D4.DelaunayFiniteSemantics

/-! The sixty actual neighbouring-cell lifting inequalities define exactly
 the positive orthant in each of the three displayed coordinate systems. -/
noncomputable section
namespace D4.Delaunay
open Analytic Matrix

theorem exists_lifting_of_count_pos (F : Fin 60 → FacetRecord) (v : Fin 10 → ℤ)
    (h : 0 < liftingCount F v) : ∃ i, (F i).lifting = v := by
  classical
  obtain ⟨i, hi⟩ := List.length_pos_iff_exists_mem.mp h
  exact ⟨i, of_decide_eq_true (List.mem_filter.mp hi).2⟩

theorem lifting1_single_exists (j : Fin 10) : ∃ i, (facets1 i).lifting=singleLifting j :=
  exists_lifting_of_count_pos _ _ (by rw [lifting1_multiplicity]; norm_num)

theorem lifting2_single_exists (j : Fin 10) : ∃ i, (facets2 i).lifting=singleLifting j := by
  refine Fin.cases ?_ (fun j => ?_) j
  · exact exists_lifting_of_count_pos _ _ (by rw [lifting2_a_multiplicity]; norm_num)
  · exact exists_lifting_of_count_pos _ _ (by rw [lifting2_single_multiplicity]; norm_num)

theorem lifting3_single_exists (j : Fin 10) : ∃ i, (facets3 i).lifting=singleLifting j := by
  refine Fin.cases ?_ (fun j => ?_) j
  · exact exists_lifting_of_count_pos _ _ (by rw [lifting3_a_multiplicity]; norm_num)
  · exact exists_lifting_of_count_pos _ _ (by rw [lifting3_single_multiplicity]; norm_num)

theorem positive_weights_of_liftings (g : Fin 10 → IntegerGram)
    (cells : Fin 24 → LatticeSimplex) (facets : Fin 60 → FacetRecord)
    (hvalid : ∀ i, facetCheck cells g (facets i)=true)
    (hsingle : ∀ j, ∃ i, (facets i).lifting=singleLifting j)
    (w : Fin 10 → ℝ) (h : ∀ i, 0 < liftingDifference g w cells (facets i)) :
    ∀ j, 0 < w j := by
  intro j
  obtain ⟨i,hi⟩ := hsingle j
  have hp := h i
  rw [liftingDifference_eq _ _ _ _ (hvalid i), hi, singleLifting_eval] at hp
  linarith

theorem facets1_positive_iff (w : Fin 10 → ℝ) :
    (∀ i, 0 < liftingDifference generators1 w cells1 (facets1 i)) ↔ ∀ j, 0 < w j :=
  ⟨positive_weights_of_liftings _ _ _ facets1_valid lifting1_single_exists w,
    fun h => facets1_positive w h⟩

theorem facets2_positive_iff (w : Fin 10 → ℝ) :
    (∀ i, 0 < liftingDifference generators2 w cells2 (facets2 i)) ↔ ∀ j, 0 < w j :=
  ⟨positive_weights_of_liftings _ _ _ facets2_valid lifting2_single_exists w,
    fun h => facets2_positive w h⟩

theorem facets3_positive_iff (w : Fin 10 → ℝ) :
    (∀ i, 0 < liftingDifference generators3 w cells3 (facets3 i)) ↔ ∀ j, 0 < w j :=
  ⟨positive_weights_of_liftings _ _ _ facets3_valid lifting3_single_exists w,
    fun h => facets3_positive w h⟩

end D4.Delaunay
