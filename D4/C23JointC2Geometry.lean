import D4.C23JointC2Partition

noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope

theorem localRegion2_subset (p q r η : ℝ) (hp : 0≤p) (hq : 0≤q) (hr : 0≤r)
    (hη : 0≤η) (i : Fin 9) : localRegion2 p q r η i ⊆ {x | gap2 p q r x≤η} := by
  intro x hx
  have h := localRegion2_affine p q r η hp hq hr i x hx
  change -lower2 r x-upper2 p q r x≤η
  rw [h.1,h.2]
  fin_cases i
  · change 0≤x 0 ∧ x 0≤2*(p+r) ∧ 0≤x 1 ∧ x 1≤2*(q+r) ∧ 2*r≤x 0+x 1 ∧ x 0+x 1≤2*(p+q+r) at hx
    rcases hx with ⟨h0,h1,h2,h3,h4,h5⟩
    change -affineEval (![0,0,0]) x-affineEval (![0,0,0]) x≤η
    simp only [affineEval_eq,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Fin.reduceFinMk,zero_mul,one_mul,zero_add,add_zero,neg_one_mul]
    linarith
  · change -η≤x 0 ∧ x 0≤0 ∧ 2*r≤x 1 ∧ x 1≤2*(q+r) at hx
    rcases hx with ⟨h0,h1,h2,h3⟩
    change -affineEval (![0,1,0]) x-affineEval (![0,0,0]) x≤η
    simp only [affineEval_eq,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Fin.reduceFinMk,zero_mul,one_mul,zero_add,add_zero,neg_one_mul]
    linarith
  · change -η≤x 1 ∧ x 1≤0 ∧ 2*r≤x 0 ∧ x 0≤2*(p+r) at hx
    rcases hx with ⟨h0,h1,h2,h3⟩
    change -affineEval (![0,0,1]) x-affineEval (![0,0,0]) x≤η
    simp only [affineEval_eq,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Fin.reduceFinMk,zero_mul,one_mul,zero_add,add_zero,neg_one_mul]
    linarith
  · change x 0≤2*r ∧ x 1≤2*r ∧ 2*r-η≤x 0+x 1 ∧ x 0+x 1≤2*r at hx
    rcases hx with ⟨h0,h1,h2,h3⟩
    change -affineEval (![-2*r,1,1]) x-affineEval (![0,0,0]) x≤η
    simp only [affineEval_eq,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Fin.reduceFinMk,zero_mul,one_mul,zero_add,add_zero,neg_one_mul]
    linarith
  · change 2*(p+r)≤x 0 ∧ x 0≤2*(p+r)+η ∧ 0≤x 1 ∧ x 1≤2*q at hx
    rcases hx with ⟨h0,h1,h2,h3⟩
    change -affineEval (![0,0,0]) x-affineEval (![2*(p+r),-1,0]) x≤η
    simp only [affineEval_eq,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Fin.reduceFinMk,zero_mul,one_mul,zero_add,add_zero,neg_one_mul]
    linarith
  · change 2*(q+r)≤x 1 ∧ x 1≤2*(q+r)+η ∧ 0≤x 0 ∧ x 0≤2*p at hx
    rcases hx with ⟨h0,h1,h2,h3⟩
    change -affineEval (![0,0,0]) x-affineEval (![2*(q+r),0,-1]) x≤η
    simp only [affineEval_eq,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Fin.reduceFinMk,zero_mul,one_mul,zero_add,add_zero,neg_one_mul]
    linarith
  · change 2*p≤x 0 ∧ 2*q≤x 1 ∧ 2*(p+q+r)≤x 0+x 1 ∧ x 0+x 1≤2*(p+q+r)+η at hx
    rcases hx with ⟨h0,h1,h2,h3⟩
    change -affineEval (![0,0,0]) x-affineEval (![2*(p+q+r),-1,-1]) x≤η
    simp only [affineEval_eq,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Fin.reduceFinMk,zero_mul,one_mul,zero_add,add_zero,neg_one_mul]
    linarith
  · change x 0≤0 ∧ 2*(q+r)≤x 1 ∧ x 1-x 0≤2*(q+r)+η at hx
    rcases hx with ⟨h0,h1,h2⟩
    change -affineEval (![0,1,0]) x-affineEval (![2*(q+r),0,-1]) x≤η
    simp only [affineEval_eq,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Fin.reduceFinMk,zero_mul,one_mul,zero_add,add_zero,neg_one_mul]
    linarith
  · change x 1≤0 ∧ 2*(p+r)≤x 0 ∧ x 0-x 1≤2*(p+r)+η at hx
    rcases hx with ⟨h0,h1,h2⟩
    change -affineEval (![0,0,1]) x-affineEval (![2*(p+r),-1,0]) x≤η
    simp only [affineEval_eq,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Fin.reduceFinMk,zero_mul,one_mul,zero_add,add_zero,neg_one_mul]
    linarith

theorem localRegion2_union (p q r η : ℝ) (hp : 0<p) (hq : 0<q) (hr : 0≤r)
    (hη : 0≤η) : (⋃ i : Fin 9,localRegion2 p q r η i)={x | gap2 p q r x≤η} :=
  subset_antisymm (iUnion_subset (localRegion2_subset p q r η hp.le hq.le hr hη))
    (localRegion2_cover p q r η hp hq hr hη)

private def integerSlopes2 (i : Fin 9) : Fin 4 → ℤ := ![
  ![0,0,0,0],![1,0,0,0],![0,1,0,0],![1,1,0,0],![0,0,-1,0],
  ![0,0,0,-1],![0,0,-1,-1],![1,0,0,-1],![0,1,-1,0]] i

private theorem integerSlopes2_injective : Function.Injective integerSlopes2 := by
  decide +kernel

private theorem realSlopes2_eq (p q r : ℝ) (i : Fin 9) :
    (![localLower2 r i 1,localLower2 r i 2,localUpper2 p q r i 1,
      localUpper2 p q r i 2] : Fin 4 → ℝ) = fun k => (integerSlopes2 i k : ℝ) := by
  ext k
  fin_cases i <;> fin_cases k
  all_goals first
    | change (0:ℝ)=((0:ℤ):ℝ)
    | change (1:ℝ)=((1:ℤ):ℝ)
    | change (-1:ℝ)=((-1:ℤ):ℝ)
  all_goals norm_num

theorem localRegion2_distinct_slopes (p q r : ℝ) (i j : Fin 9) (hij : i≠j) :
    ((localLower2 r i) 1≠(localLower2 r j) 1 ∨ (localLower2 r i) 2≠(localLower2 r j) 2) ∨
    ((localUpper2 p q r i) 1≠(localUpper2 p q r j) 1 ∨
      (localUpper2 p q r i) 2≠(localUpper2 p q r j) 2) := by
  by_contra h
  push_neg at h
  apply hij
  apply integerSlopes2_injective
  have he : (![localLower2 r i 1,localLower2 r i 2,localUpper2 p q r i 1,
      localUpper2 p q r i 2] : Fin 4 → ℝ) =
      ![localLower2 r j 1,localLower2 r j 2,localUpper2 p q r j 1,localUpper2 p q r j 2] := by
    ext k
    fin_cases k
    · exact h.1.1
    · exact h.1.2
    · exact h.2.1
    · exact h.2.2
  rw [realSlopes2_eq,realSlopes2_eq] at he
  ext k
  exact_mod_cast congrFun he k

theorem localRegion2_pairwise_null (p q r η : ℝ) (hp : 0≤p) (hq : 0≤q) (hr : 0≤r) :
    Pairwise fun i j : Fin 9 => volume
      (localRegion2 p q r η i∩localRegion2 p q r η j)=0 := by
  intro i j hij
  rcases localRegion2_distinct_slopes p q r i j hij with hl|hu
  · apply measure_mono_null (t := {x | affineEval (localLower2 r i) x=affineEval (localLower2 r j) x})
      ?_ (affineEquality_volume _ _ hl)
    intro x hx
    exact (localRegion2_affine p q r η hp hq hr i x hx.1).1.symm.trans
      (localRegion2_affine p q r η hp hq hr j x hx.2).1
  · apply measure_mono_null (t := {x | affineEval (localUpper2 p q r i) x=affineEval (localUpper2 p q r j) x})
      ?_ (affineEquality_volume _ _ hu)
    intro x hx
    exact (localRegion2_affine p q r η hp hq hr i x hx.1).2.symm.trans
      (localRegion2_affine p q r η hp hq hr j x hx.2).2

end D4.C23Local
