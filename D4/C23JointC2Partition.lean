import D4.C23LocalPartitionNullC3

/-! Nine genuine affine regions of the C1/C2 local envelope. Their union is
exactly the moving gap sublevel polygon, for all positive p,q,r and eta. -/
noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope

def localRegion2 (p q r η : ℝ) (i : Fin 9) : Set Plane := ![
  {x | 0≤x 0 ∧ x 0≤2*(p+r) ∧ 0≤x 1 ∧ x 1≤2*(q+r) ∧ 2*r≤x 0+x 1 ∧ x 0+x 1≤2*(p+q+r)},
  {x | -η≤x 0 ∧ x 0≤0 ∧ 2*r≤x 1 ∧ x 1≤2*(q+r)},
  {x | -η≤x 1 ∧ x 1≤0 ∧ 2*r≤x 0 ∧ x 0≤2*(p+r)},
  {x | x 0≤2*r ∧ x 1≤2*r ∧ 2*r-η≤x 0+x 1 ∧ x 0+x 1≤2*r},
  {x | 2*(p+r)≤x 0 ∧ x 0≤2*(p+r)+η ∧ 0≤x 1 ∧ x 1≤2*q},
  {x | 2*(q+r)≤x 1 ∧ x 1≤2*(q+r)+η ∧ 0≤x 0 ∧ x 0≤2*p},
  {x | 2*p≤x 0 ∧ 2*q≤x 1 ∧ 2*(p+q+r)≤x 0+x 1 ∧ x 0+x 1≤2*(p+q+r)+η},
  {x | x 0≤0 ∧ 2*(q+r)≤x 1 ∧ x 1-x 0≤2*(q+r)+η},
  {x | x 1≤0 ∧ 2*(p+r)≤x 0 ∧ x 0-x 1≤2*(p+r)+η}] i

def localLower2 (r : ℝ) (i : Fin 9) : Fin 3 → ℝ := ![
  ![0,0,0],![0,1,0],![0,0,1],![-2*r,1,1],![0,0,0],![0,0,0],![0,0,0],![0,1,0],![0,0,1]] i

def localUpper2 (p q r : ℝ) (i : Fin 9) : Fin 3 → ℝ := ![
  ![0,0,0],![0,0,0],![0,0,0],![0,0,0],![2*(p+r),-1,0],![2*(q+r),0,-1],![2*(p+q+r),-1,-1],![2*(q+r),0,-1],![2*(p+r),-1,0]] i

private theorem min4_choice (a b c d : ℝ) :
    min4 a b c d=a ∨ min4 a b c d=b ∨ min4 a b c d=c ∨ min4 a b c d=d := by
  rcases min_choice a (min b (min c d)) with h|h
  · exact Or.inl h
  · rcases min_choice b (min c d) with hb|hb
    · exact Or.inr (Or.inl (h.trans hb))
    · rcases min_choice c d with hc|hc
      · exact Or.inr (Or.inr (Or.inl (h.trans (hb.trans hc))))
      · exact Or.inr (Or.inr (Or.inr (h.trans (hb.trans hc))))

private theorem min4_le (a b c d : ℝ) :
    min4 a b c d≤a ∧ min4 a b c d≤b ∧ min4 a b c d≤c ∧ min4 a b c d≤d := by
  exact ⟨min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)),
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))⟩

private theorem min4_eq_of_le (a b c d t : ℝ)
    (ht : t=a ∨ t=b ∨ t=c ∨ t=d)
    (ha : t≤a) (hb : t≤b) (hc : t≤c) (hd : t≤d) : min4 a b c d=t := by
  apply le_antisymm
  · rcases ht with rfl|rfl|rfl|rfl
    · exact (min4_le _ _ _ _).1
    · exact (min4_le _ _ _ _).2.1
    · exact (min4_le _ _ _ _).2.2.1
    · exact (min4_le _ _ _ _).2.2.2
  · exact le_min ha (le_min hb (le_min hc hd))

theorem localRegion2_affine (p q r η : ℝ) (hp : 0≤p) (hq : 0≤q) (hr : 0≤r)
    (i : Fin 9) (x : Plane) (hx : x∈localRegion2 p q r η i) :
    lower2 r x=affineEval (localLower2 r i) x ∧
      upper2 p q r x=affineEval (localUpper2 p q r i) x := by
  fin_cases i
  · change 0≤x 0 ∧ x 0≤2*(p+r) ∧ 0≤x 1 ∧ x 1≤2*(q+r) ∧ 2*r≤x 0+x 1 ∧ x 0+x 1≤2*(p+q+r) at hx
    rcases hx with ⟨h0,h1,h2,h3,h4,h5⟩
    change min4 0 (x 0) (x 1) (x 0+x 1-2*r) = affineEval (![0,0,0]) x ∧
      min4 0 (2*(p+r)-x 0) (2*(q+r)-x 1) (2*(p+q)-(x 0+x 1-2*r)) = affineEval (![0,0,0]) x
    simp only [affineEval_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.reduceFinMk, zero_mul, one_mul, zero_add, add_zero, neg_one_mul]
    constructor
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inl (by ring)
      all_goals linarith
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inl (by ring)
      all_goals linarith
  · change -η≤x 0 ∧ x 0≤0 ∧ 2*r≤x 1 ∧ x 1≤2*(q+r) at hx
    rcases hx with ⟨h0,h1,h2,h3⟩
    change min4 0 (x 0) (x 1) (x 0+x 1-2*r) = affineEval (![0,1,0]) x ∧
      min4 0 (2*(p+r)-x 0) (2*(q+r)-x 1) (2*(p+q)-(x 0+x 1-2*r)) = affineEval (![0,0,0]) x
    simp only [affineEval_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.reduceFinMk, zero_mul, one_mul, zero_add, add_zero, neg_one_mul]
    constructor
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inr (Or.inl (by ring))
      all_goals linarith
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inl (by ring)
      all_goals linarith
  · change -η≤x 1 ∧ x 1≤0 ∧ 2*r≤x 0 ∧ x 0≤2*(p+r) at hx
    rcases hx with ⟨h0,h1,h2,h3⟩
    change min4 0 (x 0) (x 1) (x 0+x 1-2*r) = affineEval (![0,0,1]) x ∧
      min4 0 (2*(p+r)-x 0) (2*(q+r)-x 1) (2*(p+q)-(x 0+x 1-2*r)) = affineEval (![0,0,0]) x
    simp only [affineEval_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.reduceFinMk, zero_mul, one_mul, zero_add, add_zero, neg_one_mul]
    constructor
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inr (Or.inr (Or.inl (by ring)))
      all_goals linarith
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inl (by ring)
      all_goals linarith
  · change x 0≤2*r ∧ x 1≤2*r ∧ 2*r-η≤x 0+x 1 ∧ x 0+x 1≤2*r at hx
    rcases hx with ⟨h0,h1,h2,h3⟩
    change min4 0 (x 0) (x 1) (x 0+x 1-2*r) = affineEval (![-2*r,1,1]) x ∧
      min4 0 (2*(p+r)-x 0) (2*(q+r)-x 1) (2*(p+q)-(x 0+x 1-2*r)) = affineEval (![0,0,0]) x
    simp only [affineEval_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.reduceFinMk, zero_mul, one_mul, zero_add, add_zero, neg_one_mul]
    constructor
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inr (Or.inr (Or.inr (by ring)))
      all_goals linarith
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inl (by ring)
      all_goals linarith
  · change 2*(p+r)≤x 0 ∧ x 0≤2*(p+r)+η ∧ 0≤x 1 ∧ x 1≤2*q at hx
    rcases hx with ⟨h0,h1,h2,h3⟩
    change min4 0 (x 0) (x 1) (x 0+x 1-2*r) = affineEval (![0,0,0]) x ∧
      min4 0 (2*(p+r)-x 0) (2*(q+r)-x 1) (2*(p+q)-(x 0+x 1-2*r)) = affineEval (![2*(p+r),-1,0]) x
    simp only [affineEval_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.reduceFinMk, zero_mul, one_mul, zero_add, add_zero, neg_one_mul]
    constructor
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inl (by ring)
      all_goals linarith
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inr (Or.inl (by ring))
      all_goals linarith
  · change 2*(q+r)≤x 1 ∧ x 1≤2*(q+r)+η ∧ 0≤x 0 ∧ x 0≤2*p at hx
    rcases hx with ⟨h0,h1,h2,h3⟩
    change min4 0 (x 0) (x 1) (x 0+x 1-2*r) = affineEval (![0,0,0]) x ∧
      min4 0 (2*(p+r)-x 0) (2*(q+r)-x 1) (2*(p+q)-(x 0+x 1-2*r)) = affineEval (![2*(q+r),0,-1]) x
    simp only [affineEval_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.reduceFinMk, zero_mul, one_mul, zero_add, add_zero, neg_one_mul]
    constructor
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inl (by ring)
      all_goals linarith
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inr (Or.inr (Or.inl (by ring)))
      all_goals linarith
  · change 2*p≤x 0 ∧ 2*q≤x 1 ∧ 2*(p+q+r)≤x 0+x 1 ∧ x 0+x 1≤2*(p+q+r)+η at hx
    rcases hx with ⟨h0,h1,h2,h3⟩
    change min4 0 (x 0) (x 1) (x 0+x 1-2*r) = affineEval (![0,0,0]) x ∧
      min4 0 (2*(p+r)-x 0) (2*(q+r)-x 1) (2*(p+q)-(x 0+x 1-2*r)) = affineEval (![2*(p+q+r),-1,-1]) x
    simp only [affineEval_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.reduceFinMk, zero_mul, one_mul, zero_add, add_zero, neg_one_mul]
    constructor
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inl (by ring)
      all_goals linarith
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inr (Or.inr (Or.inr (by ring)))
      all_goals linarith
  · change x 0≤0 ∧ 2*(q+r)≤x 1 ∧ x 1-x 0≤2*(q+r)+η at hx
    rcases hx with ⟨h0,h1,h2⟩
    change min4 0 (x 0) (x 1) (x 0+x 1-2*r) = affineEval (![0,1,0]) x ∧
      min4 0 (2*(p+r)-x 0) (2*(q+r)-x 1) (2*(p+q)-(x 0+x 1-2*r)) = affineEval (![2*(q+r),0,-1]) x
    simp only [affineEval_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.reduceFinMk, zero_mul, one_mul, zero_add, add_zero, neg_one_mul]
    constructor
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inr (Or.inl (by ring))
      all_goals linarith
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inr (Or.inr (Or.inl (by ring)))
      all_goals linarith
  · change x 1≤0 ∧ 2*(p+r)≤x 0 ∧ x 0-x 1≤2*(p+r)+η at hx
    rcases hx with ⟨h0,h1,h2⟩
    change min4 0 (x 0) (x 1) (x 0+x 1-2*r) = affineEval (![0,0,1]) x ∧
      min4 0 (2*(p+r)-x 0) (2*(q+r)-x 1) (2*(p+q)-(x 0+x 1-2*r)) = affineEval (![2*(p+r),-1,0]) x
    simp only [affineEval_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.reduceFinMk, zero_mul, one_mul, zero_add, add_zero, neg_one_mul]
    constructor
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inr (Or.inr (Or.inl (by ring)))
      all_goals linarith
    · apply min4_eq_of_le _ _ _ _ _
      · exact Or.inr (Or.inl (by ring))
      all_goals linarith

theorem localRegion2_cover (p q r η : ℝ) (hp : 0<p) (hq : 0<q)
    (hr : 0≤r) (hη : 0≤η) :
    {x | gap2 p q r x≤η} ⊆ ⋃ i : Fin 9,localRegion2 p q r η i := by
  intro x hx
  have hl := min4_le 0 (x 0) (x 1) (x 0+x 1-2*r)
  have hu := min4_le 0 (2*(p+r)-x 0) (2*(q+r)-x 1) (2*(p+q)-(x 0+x 1-2*r))
  change lower2 r x≤0 ∧ lower2 r x≤x 0 ∧ lower2 r x≤x 1 ∧
    lower2 r x≤x 0+x 1-2*r at hl
  change upper2 p q r x≤0 ∧ upper2 p q r x≤2*(p+r)-x 0 ∧
    upper2 p q r x≤2*(q+r)-x 1 ∧ upper2 p q r x≤2*(p+q)-(x 0+x 1-2*r) at hu
  rcases hl with ⟨hl0,hl1,hl2,hl3⟩
  rcases hu with ⟨hu0,hu1,hu2,hu3⟩
  change -lower2 r x-upper2 p q r x≤η at hx
  have hlc := min4_choice 0 (x 0) (x 1) (x 0+x 1-2*r)
  have huc := min4_choice 0 (2*(p+r)-x 0) (2*(q+r)-x 1) (2*(p+q)-(x 0+x 1-2*r))
  change lower2 r x=0 ∨ lower2 r x=x 0 ∨ lower2 r x=x 1 ∨
    lower2 r x=x 0+x 1-2*r at hlc
  change upper2 p q r x=0 ∨ upper2 p q r x=2*(p+r)-x 0 ∨
    upper2 p q r x=2*(q+r)-x 1 ∨ upper2 p q r x=2*(p+q)-(x 0+x 1-2*r) at huc
  rcases hlc with hlc|hlc|hlc|hlc <;> rcases huc with huc|huc|huc|huc
  · apply mem_iUnion.mpr
    refine ⟨0,?_⟩
    change 0≤x 0 ∧ x 0≤2*(p+r) ∧ 0≤x 1 ∧ x 1≤2*(q+r) ∧ 2*r≤x 0+x 1 ∧ x 0+x 1≤2*(p+q+r)
    (repeat' constructor) <;> linarith
  · apply mem_iUnion.mpr
    refine ⟨4,?_⟩
    change 2*(p+r)≤x 0 ∧ x 0≤2*(p+r)+η ∧ 0≤x 1 ∧ x 1≤2*q
    (repeat' constructor) <;> linarith
  · apply mem_iUnion.mpr
    refine ⟨5,?_⟩
    change 2*(q+r)≤x 1 ∧ x 1≤2*(q+r)+η ∧ 0≤x 0 ∧ x 0≤2*p
    (repeat' constructor) <;> linarith
  · apply mem_iUnion.mpr
    refine ⟨6,?_⟩
    change 2*p≤x 0 ∧ 2*q≤x 1 ∧ 2*(p+q+r)≤x 0+x 1 ∧ x 0+x 1≤2*(p+q+r)+η
    (repeat' constructor) <;> linarith
  · apply mem_iUnion.mpr
    refine ⟨1,?_⟩
    change -η≤x 0 ∧ x 0≤0 ∧ 2*r≤x 1 ∧ x 1≤2*(q+r)
    (repeat' constructor) <;> linarith
  · exfalso
    linarith
  · apply mem_iUnion.mpr
    refine ⟨7,?_⟩
    change x 0≤0 ∧ 2*(q+r)≤x 1 ∧ x 1-x 0≤2*(q+r)+η
    (repeat' constructor) <;> linarith
  · exfalso
    linarith
  · apply mem_iUnion.mpr
    refine ⟨2,?_⟩
    change -η≤x 1 ∧ x 1≤0 ∧ 2*r≤x 0 ∧ x 0≤2*(p+r)
    (repeat' constructor) <;> linarith
  · apply mem_iUnion.mpr
    refine ⟨8,?_⟩
    change x 1≤0 ∧ 2*(p+r)≤x 0 ∧ x 0-x 1≤2*(p+r)+η
    (repeat' constructor) <;> linarith
  · exfalso
    linarith
  · exfalso
    linarith
  · apply mem_iUnion.mpr
    refine ⟨3,?_⟩
    change x 0≤2*r ∧ x 1≤2*r ∧ 2*r-η≤x 0+x 1 ∧ x 0+x 1≤2*r
    (repeat' constructor) <;> linarith
  · exfalso
    linarith
  · exfalso
    linarith
  · exfalso
    linarith

end D4.C23Local
