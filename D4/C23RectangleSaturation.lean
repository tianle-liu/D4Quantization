import D4.C23BoundaryRectangle

noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope

private theorem eight_generator_sites (n : IntVec)
    (h2 : n 2=0 ∨ n 2=1) (h3 : n 3=0 ∨ n 3=1)
    (h20 : n 2-n 0=0 ∨ n 2-n 0=1) (h30 : n 3-n 0=0 ∨ n 3-n 0=1)
    (h21 : n 2-n 1=0 ∨ n 2-n 1=1) (h31 : n 3-n 1=0 ∨ n 3-n 1=1)
    (hA : siteCost (gramMatrix ℝ) (![-2,-2,2,2] : Vec) n=0) :
    ∃ i : Fin 8, n=sites3 i := by
  rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
  · have h0 : n 0=0 ∨ n 0= -1 := by omega
    have h1 : n 1=0 ∨ n 1= -1 := by omega
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · refine ⟨0,?_⟩; ext i; fin_cases i <;> simp [sites3,h0,h1,h2,h3]
    · refine ⟨5,?_⟩; ext i; fin_cases i <;> simp [sites3,h0,h1,h2,h3]
    · refine ⟨4,?_⟩; ext i; fin_cases i <;> simp [sites3,h0,h1,h2,h3]
    · have he : n=(![-1,-1,0,0] : IntVec) := by
        ext i; fin_cases i <;> simp [h0,h1,h2,h3]
      rw [he] at hA
      norm_num [siteCost,quadratic,castVec,gramMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hA <;>
        simp only [Matrix.cons_val,Fin.reduceSucc,Fin.reduceFinMk] at hA <;> norm_num at hA
  · have h0 : n 0=0 := by omega
    have h1 : n 1=0 := by omega
    refine ⟨2,?_⟩; ext i; fin_cases i <;> simp [sites3,h0,h1,h2,h3]
  · have h0 : n 0=0 := by omega
    have h1 : n 1=0 := by omega
    refine ⟨1,?_⟩; ext i; fin_cases i <;> simp [sites3,h0,h1,h2,h3]
  · have h0 : n 0=0 ∨ n 0=1 := by omega
    have h1 : n 1=0 ∨ n 1=1 := by omega
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · refine ⟨3,?_⟩; ext i; fin_cases i <;> simp [sites3,h0,h1,h2,h3]
    · refine ⟨7,?_⟩; ext i; fin_cases i <;> simp [sites3,h0,h1,h2,h3]
    · refine ⟨6,?_⟩; ext i; fin_cases i <;> simp [sites3,h0,h1,h2,h3]
    · have he : n=(![1,1,1,1] : IntVec) := by
        ext i; fin_cases i <;> simp [h0,h1,h2,h3]
      rw [he] at hA
      norm_num [siteCost,quadratic,castVec,gramMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hA <;>
        simp only [Matrix.cons_val,Fin.reduceSucc,Fin.reduceFinMk] at hA <;> norm_num at hA

theorem rectangle_saturated_sites (w t : Fin 10 → ℝ)
    (hw : ∀ e,0≤w e) (ht : t∈Icc (-w) w) (n : IntVec)
    (hn : siteCost (principalForm w) (generatorMap t) n=0)
    (hA : siteCost (gramMatrix ℝ) (![-2,-2,2,2] : Vec) n=0)
    (hw2 : 0<w 2) (hw3 : 0<w 3) (hw5 : 0<w 5) (hw6 : 0<w 6)
    (hw7 : 0<w 7) (hw8 : 0<w 8)
    (ht2 : t 2=w 2) (ht3 : t 3=w 3) (ht5 : t 5= -(w 5))
    (ht6 : t 6= -(w 6)) (ht7 : t 7= -(w 7)) (ht8 : t 8= -(w 8)) :
    ∃ i : Fin 8,n=sites3 i := by
  have h2 := tight_generator w t hw ht n hn 2 hw2 ht2
  have h3 := tight_generator w t hw ht n hn 3 hw3 ht3
  have h5 := tight_generator_negative w t hw ht n hn 5 hw5 ht5
  have h6 := tight_generator_negative w t hw ht n hn 6 hw6 ht6
  have h7 := tight_generator_negative w t hw ht n hn 7 hw7 ht7
  have h8 := tight_generator_negative w t hw ht n hn 8 hw8 ht8
  norm_num [integerGenerators,Fin.sum_univ_succ] at h2 h3 h5 h6 h7 h8
  simp only [Matrix.cons_val,Fin.reduceSucc,Fin.reduceFinMk] at h2 h3 h5 h6 h7 h8
  norm_num at h2 h3 h5 h6 h7 h8
  exact eight_generator_sites n h2 h3 (by omega) (by omega) (by omega) (by omega) hA

theorem rectangle_sum_saturated_sites (w t : Fin 10 → ℝ) (a : ℝ)
    (hw : ∀ e,0≤w e) (ht : t∈Icc (-w) w) (ha : 0<a)
    (hw2 : 0<w 2) (hw3 : 0<w 3) (hw5 : 0<w 5) (hw6 : 0<w 6)
    (hw7 : 0<w 7) (hw8 : 0<w 8)
    (ht2 : t 2=w 2) (ht3 : t 3=w 3) (ht5 : t 5= -(w 5))
    (ht6 : t 6= -(w 6)) (ht7 : t 7= -(w 7)) (ht8 : t 8= -(w 8))
    (n : IntVec)
    (hn : siteCost (a • gramMatrix ℝ+principalForm w)
      (a • (![-2,-2,2,2] : Vec)+generatorMap t) n=0) :
    ∃ i : Fin 8,n=sites3 i := by
  have hA : 0≤siteCost (gramMatrix ℝ) (![-2,-2,2,2] : Vec) n :=
    sub_nonneg.mpr (boundary3_A_support n)
  have hP : 0≤siteCost (principalForm w) (generatorMap t) n :=
    sub_nonneg.mpr (zonotope_integer_support hw ⟨t,ht,rfl⟩ n)
  rw [siteCost_sum] at hn
  have hparts := (add_eq_zero_iff_of_nonneg (mul_nonneg ha.le hA) hP).mp hn
  have hA0 : siteCost (gramMatrix ℝ) (![-2,-2,2,2] : Vec) n=0 :=
    (mul_eq_zero.mp hparts.1).resolve_left ha.ne'
  exact rectangle_saturated_sites w t hw ht n hparts.2 hA0
    hw2 hw3 hw5 hw6 hw7 hw8 ht2 ht3 ht5 ht6 ht7 ht8

theorem rectangle_sum_saturated_sites_of_eq (Q : Gram) (r : Vec)
    (w t : Fin 10 → ℝ) (a : ℝ)
    (hQ : Q=a • gramMatrix ℝ+principalForm w)
    (hr : r=a • (![-2,-2,2,2] : Vec)+generatorMap t)
    (hw : ∀ e,0≤w e) (ht : t∈Icc (-w) w) (ha : 0<a)
    (hw2 : 0<w 2) (hw3 : 0<w 3) (hw5 : 0<w 5) (hw6 : 0<w 6)
    (hw7 : 0<w 7) (hw8 : 0<w 8)
    (ht2 : t 2=w 2) (ht3 : t 3=w 3) (ht5 : t 5= -(w 5))
    (ht6 : t 6= -(w 6)) (ht7 : t 7= -(w 7)) (ht8 : t 8= -(w 8))
    (n : IntVec) (hn : siteCost Q r n=0) : ∃ i : Fin 8,n=sites3 i := by
  rw [hQ,hr] at hn
  exact rectangle_sum_saturated_sites w t a hw ht ha hw2 hw3 hw5 hw6 hw7 hw8
    ht2 ht3 ht5 ht6 ht7 ht8 n hn

end D4.C23Local
