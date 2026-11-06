import D4.C23JointC2Geometry
import D4.AreaTrapezoidAffine
import D4.ParameterAreaAnalytic

/-! Explicit measure-preserving diagonal charts and genuine trapezoids for
the six rectangular and diagonal C2 outer regions. -/
noncomputable section
namespace D4.C23Local
open Set Matrix MeasureTheory AreaEnvelope

def diagonalEquiv2 (a b : ℝ) : Plane ≃ᵐ Plane where
  toFun x := ![a+x 1,b+x 0-x 1]
  invFun x := ![x 0+x 1-a-b,x 0-a]
  left_inv := by intro x; ext i; fin_cases i <;> dsimp <;> ring
  right_inv := by intro x; ext i; fin_cases i <;> dsimp <;> ring
  measurable_toFun := by apply Continuous.measurable; apply continuous_pi; intro i; fin_cases i <;> dsimp <;> fun_prop
  measurable_invFun := by apply Continuous.measurable; apply continuous_pi; intro i; fin_cases i <;> dsimp <;> fun_prop

theorem diagonalEquiv2_affine (a b : ℝ) (x : Plane) :
    diagonalEquiv2 a b x=![a,b]+(!![0,1;1,-1] : PlaneMatrix)*ᵥx := by
  ext i
  fin_cases i <;> simp [diagonalEquiv2,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem diagonalEquiv2_preserving (a b : ℝ) : MeasurePreserving (diagonalEquiv2 a b) volume volume := by
  constructor
  · exact (diagonalEquiv2 a b).measurable
  · have he : (diagonalEquiv2 a b : Plane → Plane)=fun x => ![a,b]+(!![0,1;1,-1] : PlaneMatrix)*ᵥx :=
      funext (diagonalEquiv2_affine a b)
    rw [he,map_planeAffine_volume _ (by norm_num [Matrix.det_fin_two])]
    norm_num [Matrix.det_fin_two]

theorem diagonalEquiv2_integral (a b : ℝ) (S : Set Plane) (f : Plane → ℝ) :
    (∫ x in diagonalEquiv2 a b '' S,f x)=∫ x in S,f (diagonalEquiv2 a b x) :=
  (diagonalEquiv2_preserving a b).setIntegral_image_emb (diagonalEquiv2 a b).measurableEmbedding f S

def rectangularTrapezoid2 (p q r η : ℝ) (i : Fin 4) : Trapezoid := ![
  Trapezoid.ofAffine (-η) η (2*r) 0 (2*(q+r)) 0,
  Trapezoid.ofAffine (2*r) (2*p) (-η) 0 0 0,
  Trapezoid.ofAffine (2*(p+r)) η 0 0 (2*q) 0,
  Trapezoid.ofAffine 0 (2*p) (2*(q+r)) 0 (2*(q+r)+η) 0] i

theorem rectangularTrapezoid2_valid (p q r η : ℝ) (hp : 0<p) (hq : 0<q)
    (hη : 0<η) (i : Fin 4) : (rectangularTrapezoid2 p q r η i).Valid := by
  fin_cases i <;> dsimp [rectangularTrapezoid2,Trapezoid.ofAffine,Trapezoid.Valid] <;>
    constructor <;> try positivity
  all_goals constructor <;> linarith

theorem rectangularRegion2_eq (p q r η : ℝ) (hp : 0<p) (hη : 0<η) (i : Fin 4) :
    localRegion2 p q r η (![1,2,4,5] i)=(rectangularTrapezoid2 p q r η i).body := by
  ext x
  fin_cases i
  all_goals dsimp only [rectangularTrapezoid2,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,Fin.reduceFinMk]
  all_goals rw [Trapezoid.ofAffine_body _ _ _ _ _ _ (by positivity)]
  all_goals dsimp [localRegion2]
  all_goals constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;>
    refine ⟨by linarith,by linarith,by linarith,by linarith⟩

def diagonalTrapezoid2 (r η : ℝ) (i : Fin 2) : Trapezoid := ![
  Trapezoid.ofAffine (-η) η 0 1 (2*r) 0,
  Trapezoid.ofAffine 0 η 0 0 (2*r) 1] i

def diagonalOffset2 (p q r : ℝ) (i : Fin 2) : Plane := ![![0,2*r],![2*p,2*(q+r)]] i

theorem diagonalTrapezoid2_valid (r η : ℝ) (hr : 0<r) (hη : 0<η) (i : Fin 2) :
    (diagonalTrapezoid2 r η i).Valid := by
  fin_cases i <;> dsimp [diagonalTrapezoid2,Trapezoid.ofAffine,Trapezoid.Valid] <;>
    constructor <;> try positivity
  all_goals constructor <;> linarith

theorem diagonalRegion2_eq (p q r η : ℝ) (hη : 0<η) (i : Fin 2) :
    localRegion2 p q r η (![3,6] i)=
      diagonalEquiv2 (diagonalOffset2 p q r i 0) (diagonalOffset2 p q r i 1) ''
        (diagonalTrapezoid2 r η i).body := by
  ext x
  have he (e : Plane ≃ᵐ Plane) (S : Set Plane) : x∈e '' S ↔ e.symm x∈S := by
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [MeasurableEquiv.symm_apply_apply] using hy
    · intro hx
      exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
  rw [he]
  fin_cases i
  all_goals dsimp only [diagonalTrapezoid2,diagonalOffset2,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
  all_goals rw [Trapezoid.ofAffine_body _ _ _ _ _ _ hη]
  all_goals dsimp [localRegion2,diagonalEquiv2]
  all_goals constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;>
    refine ⟨by linarith,by linarith,by linarith,by linarith⟩

end D4.C23Local
