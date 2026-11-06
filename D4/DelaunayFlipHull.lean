import D4.PrincipalSimplexHull

/-! A parallelogram circuit may be triangulated using either diagonal. -/
noncomputable section
namespace D4.Delaunay
open Matrix Analytic Principal Set

 theorem convexHull_range_weights {m : ℕ} (v : Fin m → Vec) {x : Vec}
    (hx : x ∈ convexHull ℝ (range v)) :
    ∃ w : Fin m → ℝ, (∀ i,0 ≤ w i) ∧ (∑ i,w i)=1 ∧ (∑ i,w i • v i)=x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s,w,hw,hs,hx⟩ := hx
  refine ⟨fun i => if i ∈ s then w i else 0,?_,?_,?_⟩
  · intro i
    dsimp only
    split_ifs with hi
    · exact hw i hi
    · exact le_refl 0
  · simpa using hs
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ hs] at hx
    simpa only [ite_smul,zero_smul,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const_zero,add_zero] using hx

 theorem quadrilateral_join_diagonal (a b c d V W : Vec)
    (hrel : a+c=b+d) :
    convexHull ℝ (range ![a,b,c,d,V,W])=
      vertexSimplex ![a,b,c,V,W] ∪ vertexSimplex ![a,d,c,V,W] := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨w,hw,hs,hx⟩ := convexHull_range_weights ![a,b,c,d,V,W] hx
    have hs' : w 0+w 1+w 2+w 3+w 4+w 5=1 := by
      simpa [Fin.sum_univ_succ,add_assoc] using hs
    by_cases h : w 3 ≤ w 1
    · apply Or.inl
      rw [vertexSimplex_eq_convexHull]
      apply mem_convexHull_of_exists_fintype
        (![w 0+w 3,w 1-w 3,w 2+w 3,w 4,w 5] : Fin 5 → ℝ) ![a,b,c,V,W]
      · intro i
        fin_cases i <;> norm_num <;>
          linarith [hw 0,hw 1,hw 2,hw 3,hw 4,hw 5]
      · norm_num [Fin.sum_univ_succ]
        linarith
      · intro i
        exact ⟨i,rfl⟩
      · rw [← hx]
        ext k
        have hk := congrFun hrel k
        simp only [Pi.add_apply] at hk
        norm_num [Fin.sum_univ_succ,Pi.smul_apply,Finset.sum_apply,Fin.succ]
        change (w 0+w 3)*a k+((w 1-w 3)*b k+((w 2+w 3)*c k+(w 4*V k+w 5*W k))) =
          w 0*a k+(w 1*b k+(w 2*c k+(w 3*d k+(w 4*V k+w 5*W k))))
        linear_combination (w 3)*hk
    · have hh : w 1 ≤ w 3 := le_of_lt (lt_of_not_ge h)
      apply Or.inr
      rw [vertexSimplex_eq_convexHull]
      apply mem_convexHull_of_exists_fintype
        (![w 0+w 1,w 3-w 1,w 2+w 1,w 4,w 5] : Fin 5 → ℝ) ![a,d,c,V,W]
      · intro i
        fin_cases i <;> norm_num <;>
          linarith [hw 0,hw 1,hw 2,hw 3,hw 4,hw 5]
      · norm_num [Fin.sum_univ_succ]
        linarith
      · intro i
        exact ⟨i,rfl⟩
      · rw [← hx]
        ext k
        have hk := congrFun hrel k
        simp only [Pi.add_apply] at hk
        norm_num [Fin.sum_univ_succ,Pi.smul_apply,Finset.sum_apply,Fin.succ]
        change (w 0+w 1)*a k+((w 3-w 1)*d k+((w 2+w 1)*c k+(w 4*V k+w 5*W k))) =
          w 0*a k+(w 1*b k+(w 2*c k+(w 3*d k+(w 4*V k+w 5*W k))))
        linear_combination (w 1)*hk
  · apply union_subset
    · rw [vertexSimplex_eq_convexHull]
      apply convexHull_mono
      simp only [Matrix.range_cons,Matrix.range_empty,Set.union_empty]
      intro x hx
      simp only [Set.mem_union,Set.mem_singleton_iff] at *
      tauto
    · rw [vertexSimplex_eq_convexHull]
      apply convexHull_mono
      simp only [Matrix.range_cons,Matrix.range_empty,Set.union_empty]
      intro x hx
      simp only [Set.mem_union,Set.mem_singleton_iff] at *
      tauto

 theorem quadrilateral_join_other_diagonal (a b c d V W : Vec)
    (hrel : a+c=b+d) :
    convexHull ℝ (range ![a,b,c,d,V,W])=
      vertexSimplex ![a,b,d,V,W] ∪ vertexSimplex ![b,c,d,V,W] := by
  have h := quadrilateral_join_diagonal b a d c V W hrel.symm
  have hwhole : range ![b,a,d,c,V,W]=range ![a,b,c,d,V,W] := by
    ext x
    simp only [Matrix.range_cons,Matrix.range_empty,Set.union_empty,Set.mem_union,Set.mem_singleton_iff]
    tauto
  have hfirst : range ![b,a,d,V,W]=range ![a,b,d,V,W] := by
    ext x
    simp only [Matrix.range_cons,Matrix.range_empty,Set.union_empty,Set.mem_union,Set.mem_singleton_iff]
    tauto
  simpa only [vertexSimplex_eq_convexHull,hwhole,hfirst] using h

 theorem quadrilateral_flip_same_region (a b c d V W : Vec)
    (hrel : a+c=b+d) :
    vertexSimplex ![a,b,c,V,W] ∪ vertexSimplex ![a,d,c,V,W]=
      vertexSimplex ![a,b,d,V,W] ∪ vertexSimplex ![b,c,d,V,W] := by
  rw [← quadrilateral_join_diagonal _ _ _ _ _ _ hrel,
    quadrilateral_join_other_diagonal _ _ _ _ _ _ hrel]

end D4.Delaunay
