import D4.AreaTriangleHull
import D4.AreaPolygonSeparation

/-! A genuine trapezoid is split into two nondegenerate actual triangles.
Only positive width and positive endpoint heights are assumed. -/
noncomputable section
namespace D4.AreaEnvelope
open Set Matrix MeasureTheory

structure Trapezoid where
  left : ℝ
  width : ℝ
  bottomLeft : ℝ
  bottomRight : ℝ
  topLeft : ℝ
  topRight : ℝ

def Trapezoid.Valid (T : Trapezoid) : Prop :=
  0<T.width ∧ T.bottomLeft<T.topLeft ∧ T.bottomRight<T.topRight

def Trapezoid.parameter (T : Trapezoid) (x : Plane) : ℝ := (x 0-T.left)/T.width

def Trapezoid.body (T : Trapezoid) : Set Plane := {x |
  0≤T.parameter x ∧ T.parameter x≤1 ∧
  T.bottomLeft+(T.bottomRight-T.bottomLeft)*T.parameter x≤x 1 ∧
  x 1≤T.topLeft+(T.topRight-T.topLeft)*T.parameter x}

def Trapezoid.origin (T : Trapezoid) : Plane := ![T.left,T.bottomLeft]
def Trapezoid.matrix (T : Trapezoid) (i : Fin 2) : PlaneMatrix :=
  if i=0 then !![T.width,T.width;T.bottomRight-T.bottomLeft,T.topRight-T.bottomLeft]
  else !![T.width,0;T.topRight-T.bottomLeft,T.topLeft-T.bottomLeft]

theorem affineTriangle_mem_coordinates (B : PlaneMatrix) (c x : Plane) :
    x∈affineTriangle B c ↔ ∃ a b : ℝ,0≤a ∧ 0≤b ∧ a+b≤1 ∧
      c 0+B 0 0*a+B 0 1*b=x 0 ∧ c 1+B 1 0*a+B 1 1*b=x 1 := by
  constructor
  · rintro ⟨u,hu,rfl⟩
    refine ⟨u 0,u 1,hu.1 0,hu.1 1,?_,?_,?_⟩
    · simpa [Fin.sum_univ_succ] using hu.2
    · simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]; ring
    · simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ]; ring
  · rintro ⟨a,b,ha,hb,hs,h0,h1⟩
    refine ⟨![a,b],?_,?_⟩
    · constructor
      · intro i; fin_cases i <;> assumption
      · simpa [Fin.sum_univ_succ] using hs
    · ext i; fin_cases i
      · simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,add_assoc] using h0
      · simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,add_assoc] using h1

theorem Trapezoid.first_mem_iff (T : Trapezoid) (hT : T.Valid) (x : Plane) :
    x∈affineTriangle (T.matrix 0) T.origin ↔
      0≤T.parameter x ∧ T.parameter x≤1 ∧
      T.bottomLeft+(T.bottomRight-T.bottomLeft)*T.parameter x≤x 1 ∧
      x 1≤T.bottomLeft+(T.topRight-T.bottomLeft)*T.parameter x := by
  have hw := hT.1
  have hh : 0<T.topRight-T.bottomRight := sub_pos.mpr hT.2.2
  have hx : T.width*T.parameter x=x 0-T.left := by
    unfold parameter
    field_simp
  rw [affineTriangle_mem_coordinates]
  change (∃ a b : ℝ,0≤a ∧ 0≤b ∧ a+b≤1 ∧
    T.left+T.width*a+T.width*b=x 0 ∧
    T.bottomLeft+(T.bottomRight-T.bottomLeft)*a+(T.topRight-T.bottomLeft)*b=x 1) ↔ _
  constructor
  · rintro ⟨a,b,ha,hb,hab,he0,he1⟩
    have hs : T.parameter x=a+b := by nlinarith
    rw [hs]
    refine ⟨by positivity,hab,?_,?_⟩
    · nlinarith
    · nlinarith
  · rintro ⟨hs0,hs1,hbot,htop⟩
    let b := (x 1-T.bottomLeft-(T.bottomRight-T.bottomLeft)*T.parameter x)/(T.topRight-T.bottomRight)
    have he : (T.topRight-T.bottomRight)*b=x 1-T.bottomLeft-(T.bottomRight-T.bottomLeft)*T.parameter x := by
      dsimp [b]
      field_simp
    have hb : 0≤b := div_nonneg (by linarith) hh.le
    have hbs : b≤T.parameter x := by nlinarith
    refine ⟨T.parameter x-b,b,by linarith,hb,by linarith,?_,?_⟩
    · nlinarith
    · nlinarith

theorem Trapezoid.second_mem_iff (T : Trapezoid) (hT : T.Valid) (x : Plane) :
    x∈affineTriangle (T.matrix 1) T.origin ↔
      0≤T.parameter x ∧ T.parameter x≤1 ∧
      T.bottomLeft+(T.topRight-T.bottomLeft)*T.parameter x≤x 1 ∧
      x 1≤T.topLeft+(T.topRight-T.topLeft)*T.parameter x := by
  have hw := hT.1
  have hh : 0<T.topLeft-T.bottomLeft := sub_pos.mpr hT.2.1
  have hx : T.width*T.parameter x=x 0-T.left := by
    unfold parameter
    field_simp
  rw [affineTriangle_mem_coordinates]
  change (∃ a b : ℝ,0≤a ∧ 0≤b ∧ a+b≤1 ∧
    T.left+T.width*a+0*b=x 0 ∧
    T.bottomLeft+(T.topRight-T.bottomLeft)*a+(T.topLeft-T.bottomLeft)*b=x 1) ↔ _
  simp only [zero_mul,add_zero]
  constructor
  · rintro ⟨a,b,ha,hb,hab,he0,he1⟩
    have hs : T.parameter x=a := by nlinarith
    rw [hs]
    refine ⟨ha,by linarith,?_,?_⟩
    · nlinarith
    · nlinarith
  · rintro ⟨hs0,hs1,hbot,htop⟩
    let b := (x 1-T.bottomLeft-(T.topRight-T.bottomLeft)*T.parameter x)/(T.topLeft-T.bottomLeft)
    have he : (T.topLeft-T.bottomLeft)*b=x 1-T.bottomLeft-(T.topRight-T.bottomLeft)*T.parameter x := by
      dsimp [b]
      field_simp
    have hb : 0≤b := div_nonneg (by linarith) hh.le
    have hbs : T.parameter x+b≤1 := by nlinarith
    refine ⟨T.parameter x,b,hs0,hb,hbs,?_,?_⟩
    · linarith
    · nlinarith

theorem Trapezoid.cover (T : Trapezoid) (hT : T.Valid) :
    (⋃ i : Fin 2,affineTriangle (T.matrix i) T.origin)=T.body := by
  ext x
  simp only [Set.mem_iUnion,Fin.exists_fin_two,first_mem_iff T hT,second_mem_iff T hT,body,mem_setOf_eq]
  constructor
  · rintro (⟨h0,h1,hb,ht⟩ | ⟨h0,h1,hb,ht⟩)
    · refine ⟨h0,h1,hb,?_⟩
      nlinarith [hT.2.1]
    · refine ⟨h0,h1,?_,ht⟩
      nlinarith [hT.2.2]
  · rintro ⟨h0,h1,hb,ht⟩
    by_cases hd : x 1≤T.bottomLeft+(T.topRight-T.bottomLeft)*T.parameter x
    · exact Or.inl ⟨h0,h1,hb,hd⟩
    · exact Or.inr ⟨h0,h1,le_of_lt (lt_of_not_ge hd),ht⟩

end D4.AreaEnvelope
