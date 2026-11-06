import D4.C23SublevelGeometry
import D4.AreaPolygonSeparation

/-! The actual common affine regions of the C₂/C₃ local envelope in a fixed
rectangular neighborhood. There are seven regions; their intersections are null. -/
noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope

def localRegion3 (A B η ρ : ℝ) (i : Fin 7) : Set Plane := ![
  {x | 0≤x 0 ∧ x 0≤A ∧ 0≤x 1 ∧ x 1≤B},
  {x | -η≤x 0 ∧ x 0≤0 ∧ x 0≤x 1 ∧ x 1≤B},
  {x | -η≤x 1 ∧ x 1≤0 ∧ x 1≤x 0 ∧ x 0≤A},
  {x | A≤x 0 ∧ x 0≤A+ρ ∧ 0≤x 1 ∧ x 1≤B+x 0-A},
  {x | B≤x 1 ∧ x 1≤B+ρ ∧ 0≤x 0 ∧ x 0≤A+x 1-B},
  {x | -η≤x 0 ∧ x 0≤0 ∧ B≤x 1 ∧ x 1≤B+ρ},
  {x | A≤x 0 ∧ x 0≤A+ρ ∧ -η≤x 1 ∧ x 1≤0}] i

def localRectangle3 (A B η ρ : ℝ) : Set Plane := Icc ![-η,-η] ![A+ρ,B+ρ]

theorem localRegion3_subset (A B η ρ : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hη : 0≤η) (hρ : 0≤ρ) (i : Fin 7) :
    localRegion3 A B η ρ i⊆localRectangle3 A B η ρ := by
  intro x hx
  fin_cases i <;> dsimp [localRegion3] at hx <;> rcases hx with ⟨h1,h2,h3,h4⟩ <;>
    constructor <;> intro j <;> fin_cases j <;> dsimp [localRectangle3] <;> linarith

theorem localRegion3_cover (A B η ρ : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hη : 0≤η) (hρ : 0≤ρ) :
    (⋃ i : Fin 7,localRegion3 A B η ρ i)=localRectangle3 A B η ρ := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun i => localRegion3_subset A B η ρ hA hB hη hρ i
  · intro x hx
    have hlx : -η≤x 0 := hx.1 0
    have hly : -η≤x 1 := hx.1 1
    have hux : x 0≤A+ρ := hx.2 0
    have huy : x 1≤B+ρ := hx.2 1
    by_cases hx0 : x 0≤0
    · by_cases hxy : x 0≤x 1
      · by_cases hyB : x 1≤B
        · exact Set.mem_iUnion.mpr ⟨1,hlx,hx0,hxy,hyB⟩
        · exact Set.mem_iUnion.mpr ⟨5,hlx,hx0,by linarith,huy⟩
      · exact Set.mem_iUnion.mpr ⟨2,hly,by linarith,by linarith,by linarith⟩
    · by_cases hy0 : x 1≤0
      · by_cases hxA : x 0≤A
        · exact Set.mem_iUnion.mpr ⟨2,hly,hy0,by linarith,hxA⟩
        · exact Set.mem_iUnion.mpr ⟨6,by linarith,hux,hly,hy0⟩
      · by_cases hxA : x 0≤A
        · by_cases hyB : x 1≤B
          · exact Set.mem_iUnion.mpr ⟨0,by linarith,hxA,by linarith,hyB⟩
          · exact Set.mem_iUnion.mpr ⟨4,by linarith,huy,by linarith,by linarith⟩
        · by_cases hd : x 1≤B+x 0-A
          · exact Set.mem_iUnion.mpr ⟨3,by linarith,hux,by linarith,hd⟩
          · exact Set.mem_iUnion.mpr ⟨4,by linarith,huy,by linarith,by linarith⟩

def localLower3 (i : Fin 7) : Fin 3 → ℝ := ![
  ![0,0,0],![0,1,0],![0,0,1],![0,0,0],![0,0,0],![0,1,0],![0,0,1]] i

def localUpper3 (A B : ℝ) (i : Fin 7) : Fin 3 → ℝ := ![
  ![0,0,0],![0,0,0],![0,0,0],![A,-1,0],![B,0,-1],![B,0,-1],![A,-1,0]] i

private theorem min3_eq_first {a b c : ℝ} (hb : a≤b) (hc : a≤c) : min3 a b c=a :=
  min_eq_left (le_min hb hc)
private theorem min3_eq_second {a b c : ℝ} (hb : b≤a) (hc : b≤c) : min3 a b c=b := by
  rw [min3,min_eq_left hc,min_eq_right hb]
private theorem min3_eq_third {a b c : ℝ} (ha : c≤a) (hb : c≤b) : min3 a b c=c := by
  rw [min3,min_eq_right hb,min_eq_right ha]

theorem localRegion3_affine (A B η ρ : ℝ) (hA : 0≤A) (hB : 0≤B)
    (i : Fin 7) (x : Plane) (hx : x∈localRegion3 A B η ρ i) :
    lower3 x=affineEval (localLower3 i) x ∧
      upper3 A B x=affineEval (localUpper3 A B i) x := by
  simp only [affineEval_eq]
  fin_cases i
  · dsimp [localRegion3] at hx
    rcases hx with ⟨h1,h2,h3,h4⟩
    change min3 0 (x 0) (x 1) = 0+0*x 0+0*x 1 ∧
      min3 0 (A-x 0) (B-x 1) = 0+0*x 0+0*x 1
    simp only [zero_mul,one_mul,zero_add,add_zero,neg_one_mul,← sub_eq_add_neg]
    exact ⟨min3_eq_first h1 h3,min3_eq_first (by linarith) (by linarith)⟩
  · dsimp [localRegion3] at hx
    rcases hx with ⟨h1,h2,h3,h4⟩
    change min3 0 (x 0) (x 1) = 0+1*x 0+0*x 1 ∧
      min3 0 (A-x 0) (B-x 1) = 0+0*x 0+0*x 1
    simp only [zero_mul,one_mul,zero_add,add_zero,neg_one_mul,← sub_eq_add_neg]
    exact ⟨min3_eq_second h2 h3,min3_eq_first (by linarith) (by linarith)⟩
  · dsimp [localRegion3] at hx
    rcases hx with ⟨h1,h2,h3,h4⟩
    change min3 0 (x 0) (x 1) = 0+0*x 0+1*x 1 ∧
      min3 0 (A-x 0) (B-x 1) = 0+0*x 0+0*x 1
    simp only [zero_mul,one_mul,zero_add,add_zero,neg_one_mul,← sub_eq_add_neg]
    exact ⟨min3_eq_third h2 h3,min3_eq_first (by linarith) (by linarith)⟩
  · dsimp [localRegion3] at hx
    rcases hx with ⟨h1,h2,h3,h4⟩
    change min3 0 (x 0) (x 1) = 0+0*x 0+0*x 1 ∧
      min3 0 (A-x 0) (B-x 1) = A+(-1)*x 0+0*x 1
    simp only [zero_mul,one_mul,zero_add,add_zero,neg_one_mul,← sub_eq_add_neg]
    exact ⟨min3_eq_first (by linarith) h3,min3_eq_second (by linarith) (by linarith)⟩
  · dsimp [localRegion3] at hx
    rcases hx with ⟨h1,h2,h3,h4⟩
    change min3 0 (x 0) (x 1) = 0+0*x 0+0*x 1 ∧
      min3 0 (A-x 0) (B-x 1) = B+0*x 0+(-1)*x 1
    simp only [zero_mul,one_mul,zero_add,add_zero,neg_one_mul,← sub_eq_add_neg]
    exact ⟨min3_eq_first h3 (by linarith),min3_eq_third (by linarith) (by linarith)⟩
  · dsimp [localRegion3] at hx
    rcases hx with ⟨h1,h2,h3,h4⟩
    change min3 0 (x 0) (x 1) = 0+1*x 0+0*x 1 ∧
      min3 0 (A-x 0) (B-x 1) = B+0*x 0+(-1)*x 1
    simp only [zero_mul,one_mul,zero_add,add_zero,neg_one_mul,← sub_eq_add_neg]
    exact ⟨min3_eq_second h2 (by linarith),min3_eq_third (by linarith) (by linarith)⟩
  · dsimp [localRegion3] at hx
    rcases hx with ⟨h1,h2,h3,h4⟩
    change min3 0 (x 0) (x 1) = 0+0*x 0+1*x 1 ∧
      min3 0 (A-x 0) (B-x 1) = A+(-1)*x 0+0*x 1
    simp only [zero_mul,one_mul,zero_add,add_zero,neg_one_mul,← sub_eq_add_neg]
    exact ⟨min3_eq_third h4 (by linarith),min3_eq_second (by linarith) (by linarith)⟩

end D4.C23Local
