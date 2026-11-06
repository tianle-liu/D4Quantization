import D4.C23JointC2Geometry
import D4.AreaTrapezoidAffine

/-! Three actual parallelograms tile the central C2 hexagon, with null overlap. -/
noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope

def centralRegion2 (p q r : ℝ) (i : Fin 3) : Set Plane := ![
  {x | 2*r≤x 0 ∧ x 0≤2*(p+r) ∧ 0≤x 1 ∧ x 1≤2*q},
  {x | 0≤x 0 ∧ x 0≤2*r ∧ 2*r-x 0≤x 1 ∧ x 1≤2*(q+r)-x 0},
  {x | 2*q≤x 1 ∧ x 1≤2*(q+r) ∧ 2*(q+r)-x 1≤x 0 ∧
    x 0≤2*(p+q+r)-x 1}] i

theorem centralRegion2_subset (p q r η : ℝ) (hp : 0≤p) (hq : 0≤q) (hr : 0≤r)
    (i : Fin 3) : centralRegion2 p q r i ⊆ localRegion2 p q r η 0 := by
  intro x hx
  change 0≤x 0 ∧ x 0≤2*(p+r) ∧ 0≤x 1 ∧ x 1≤2*(q+r) ∧
    2*r≤x 0+x 1 ∧ x 0+x 1≤2*(p+q+r)
  fin_cases i <;> dsimp [centralRegion2] at hx <;> rcases hx with ⟨h1,h2,h3,h4⟩ <;>
    (repeat' constructor) <;> linarith

theorem centralRegion2_cover (p q r η : ℝ) (hp : 0≤p) (hq : 0≤q) (hr : 0≤r) :
    (⋃ i : Fin 3,centralRegion2 p q r i)=localRegion2 p q r η 0 := by
  apply subset_antisymm
  · exact iUnion_subset (centralRegion2_subset p q r η hp hq hr)
  · intro x hx
    change 0≤x 0 ∧ x 0≤2*(p+r) ∧ 0≤x 1 ∧ x 1≤2*(q+r) ∧
      2*r≤x 0+x 1 ∧ x 0+x 1≤2*(p+q+r) at hx
    rcases hx with ⟨h1,h2,h3,h4,h5,h6⟩
    by_cases hx0 : x 0≤2*r
    · by_cases hs : x 0+x 1≤2*(q+r)
      · exact mem_iUnion.mpr ⟨1,h1,hx0,by linarith,by linarith⟩
      · exact mem_iUnion.mpr ⟨2,by linarith,h4,by linarith,by linarith⟩
    · by_cases hy : x 1≤2*q
      · exact mem_iUnion.mpr ⟨0,by linarith,h2,h3,hy⟩
      · exact mem_iUnion.mpr ⟨2,by linarith,h4,by linarith,by linarith⟩

private theorem plane_coordinate_null (a b c : ℝ) (h : a≠0 ∨ b≠0) :
    volume {x : Plane | a*x 0+b*x 1=c}=0 := by
  have he : {x : Plane | a*x 0+b*x 1=c} =
      {x : Plane | affineEval (![-c,a,b]) x=affineEval (![0,0,0]) x} := by
    ext x
    simp only [mem_setOf_eq,affineEval_eq,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,zero_mul,zero_add]
    constructor <;> intro hx <;> linarith
  rw [he]
  exact affineEquality_volume _ _ h

theorem centralRegion2_pairwise_null (p q r : ℝ) : Pairwise fun i j : Fin 3 =>
    volume (centralRegion2 p q r i∩centralRegion2 p q r j)=0 := by
  have h01 : volume (centralRegion2 p q r 0∩centralRegion2 p q r 1)=0 := by
    apply measure_mono_null (t := {x : Plane | (1:ℝ)*x 0+0*x 1=2*r}) ?_
      (plane_coordinate_null 1 0 (2*r) (Or.inl (by norm_num)))
    intro x hx
    change (2*r≤x 0 ∧ x 0≤2*(p+r) ∧ 0≤x 1 ∧ x 1≤2*q) ∧
      (0≤x 0 ∧ x 0≤2*r ∧ 2*r-x 0≤x 1 ∧ x 1≤2*(q+r)-x 0) at hx
    change 1*x 0+0*x 1=2*r
    linarith [hx.1.1,hx.2.2.1]
  have h02 : volume (centralRegion2 p q r 0∩centralRegion2 p q r 2)=0 := by
    apply measure_mono_null (t := {x : Plane | (0:ℝ)*x 0+1*x 1=2*q}) ?_
      (plane_coordinate_null 0 1 (2*q) (Or.inr (by norm_num)))
    intro x hx
    change (2*r≤x 0 ∧ x 0≤2*(p+r) ∧ 0≤x 1 ∧ x 1≤2*q) ∧
      (2*q≤x 1 ∧ x 1≤2*(q+r) ∧ 2*(q+r)-x 1≤x 0 ∧ x 0≤2*(p+q+r)-x 1) at hx
    change 0*x 0+1*x 1=2*q
    linarith [hx.1.2.2.2,hx.2.1]
  have h12 : volume (centralRegion2 p q r 1∩centralRegion2 p q r 2)=0 := by
    apply measure_mono_null (t := {x : Plane | (1:ℝ)*x 0+1*x 1=2*(q+r)}) ?_
      (plane_coordinate_null 1 1 (2*(q+r)) (Or.inl (by norm_num)))
    intro x hx
    change (0≤x 0 ∧ x 0≤2*r ∧ 2*r-x 0≤x 1 ∧ x 1≤2*(q+r)-x 0) ∧
      (2*q≤x 1 ∧ x 1≤2*(q+r) ∧ 2*(q+r)-x 1≤x 0 ∧ x 0≤2*(p+q+r)-x 1) at hx
    change 1*x 0+1*x 1=2*(q+r)
    linarith [hx.1.2.2.2,hx.2.2.2.1]
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h01
  · exact h02
  · rw [inter_comm]
    exact h01
  · exact (hij rfl).elim
  · exact h12
  · rw [inter_comm]
    exact h02
  · rw [inter_comm]
    exact h12
  · exact (hij rfl).elim

end D4.C23Local
