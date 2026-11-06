import D4.C23JointC2Charts

noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope

def cornerMatrix2 (η : ℝ) (i : Fin 2) : PlaneMatrix :=
  ![!![-η,0;0,η],!![η,0;0,-η]] i

def cornerOrigin2 (p q r : ℝ) (i : Fin 2) : Plane :=
  ![![0,2*(q+r)],![2*(p+r),0]] i

theorem cornerMatrix2_det (η : ℝ) (i : Fin 2) : (cornerMatrix2 η i).det= -η^2 := by
  fin_cases i <;> simp [cornerMatrix2,Matrix.det_fin_two] <;> ring

theorem cornerRegion2_eq (p q r η : ℝ) (hη : 0<η) (i : Fin 2) :
    localRegion2 p q r η (![7,8] i)=affineTriangle (cornerMatrix2 η i) (cornerOrigin2 p q r i) := by
  ext x
  rw [affineTriangle_mem_coordinates]
  fin_cases i
  · change (x 0≤0 ∧ 2*(q+r)≤x 1 ∧ x 1-x 0≤2*(q+r)+η) ↔
      ∃ a b : ℝ,0≤a ∧ 0≤b ∧ a+b≤1 ∧
        0+(-η)*a+0*b=x 0 ∧ 2*(q+r)+0*a+η*b=x 1
    constructor
    · rintro ⟨h0,h1,h2⟩
      let a := -x 0/η
      let b := (x 1-2*(q+r))/η
      have ha : η*a= -x 0 := by dsimp [a]; field_simp <;> ring
      have hb : η*b=x 1-2*(q+r) := by dsimp [b]; field_simp <;> ring
      refine ⟨a,b,div_nonneg (by linarith) hη.le,
        div_nonneg (by linarith) hη.le,?_,?_,?_⟩ <;> nlinarith
    · rintro ⟨a,b,ha,hb,hs,h0,h1⟩
      refine ⟨?_,?_,?_⟩ <;> nlinarith
  · change (x 1≤0 ∧ 2*(p+r)≤x 0 ∧ x 0-x 1≤2*(p+r)+η) ↔
      ∃ a b : ℝ,0≤a ∧ 0≤b ∧ a+b≤1 ∧
        2*(p+r)+η*a+0*b=x 0 ∧ 0+0*a+(-η)*b=x 1
    constructor
    · rintro ⟨h0,h1,h2⟩
      let a := (x 0-2*(p+r))/η
      let b := -x 1/η
      have ha : η*a=x 0-2*(p+r) := by dsimp [a]; field_simp <;> ring
      have hb : η*b= -x 1 := by dsimp [b]; field_simp <;> ring
      refine ⟨a,b,div_nonneg (by linarith) hη.le,
        div_nonneg (by linarith) hη.le,?_,?_,?_⟩ <;> nlinarith
    · rintro ⟨a,b,ha,hb,hs,h0,h1⟩
      refine ⟨?_,?_,?_⟩ <;> nlinarith

end D4.C23Local
