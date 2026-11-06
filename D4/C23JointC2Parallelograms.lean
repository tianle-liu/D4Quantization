import D4.C23JointWindowAffine
import D4.C23JointC2Central
import D4.C23JointC2Charts
import D4.AreaPlaneSwap

/-! The central hexagon and the four rectangular outer C2 regions have
genuine affine square charts, with jointly analytic quadratic integrals. -/
noncomputable section
namespace D4.C23Local
open Analytic AreaEnvelope Matrix MeasureTheory Set Filter Topology

def planeUnitSquare : Set Plane := Icc 0 1

theorem affineSquare_mem_coordinates (B : PlaneMatrix) (c x : Plane) :
    x∈(fun y => c+B*ᵥy) '' planeUnitSquare ↔
      ∃ a b : ℝ,0≤a ∧ a≤1 ∧ 0≤b ∧ b≤1 ∧
        c 0+B 0 0*a+B 0 1*b=x 0 ∧ c 1+B 1 0*a+B 1 1*b=x 1 := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    refine ⟨y 0,y 1,hy.1 0,hy.2 0,hy.1 1,hy.2 1,?_,?_⟩ <;>
      simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring
  · rintro ⟨a,b,ha,ha',hb,hb',h0,h1⟩
    refine ⟨![a,b],⟨?_,?_⟩,?_⟩
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
    · ext i; fin_cases i
      · simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,add_assoc] using h0
      · simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,add_assoc] using h1

def stripMatrix (w b m t : ℝ) : PlaneMatrix := !![w,0;m*w,t-b]
def stripOrigin (l b m : ℝ) : Plane := ![l,b+m*l]

theorem equalSlopeTrapezoid_affine_square (l w b m t : ℝ) (hw : 0<w) (ht : b<t) :
    (Trapezoid.ofAffine l w b m t m).body=
      (fun y => stripOrigin l b m+stripMatrix w b m t*ᵥy) '' planeUnitSquare := by
  ext x
  rw [Trapezoid.ofAffine_body _ _ _ _ _ _ hw,affineSquare_mem_coordinates]
  change (l≤x 0 ∧ x 0≤l+w ∧ b+m*x 0≤x 1 ∧ x 1≤t+m*x 0) ↔
    ∃ a d : ℝ,0≤a ∧ a≤1 ∧ 0≤d ∧ d≤1 ∧
      l+w*a+0*d=x 0 ∧ b+m*l+(m*w)*a+(t-b)*d=x 1
  constructor
  · rintro ⟨h0,h1,h2,h3⟩
    let a := (x 0-l)/w
    let d := (x 1-b-m*x 0)/(t-b)
    have ha : w*a=x 0-l := by dsimp [a]; field_simp
    have hd : (t-b)*d=x 1-b-m*x 0 := by
      dsimp [d]
      field_simp [ne_of_gt (sub_pos.mpr ht)]
    have hm := congrArg (fun s : ℝ => m*s) ha
    dsimp only at hm
    ring_nf at hm
    refine ⟨a,d,div_nonneg (by linarith) hw.le,?_,
      div_nonneg (by linarith) (sub_pos.mpr ht).le,?_,?_,?_⟩ <;> nlinarith
  · rintro ⟨a,d,ha,ha',hd,hd',h0,h1⟩
    have hm := congrArg (fun s : ℝ => m*s) h0
    dsimp only at hm
    ring_nf at hm
    refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

def swapPlaneMatrix (B : PlaneMatrix) : PlaneMatrix := !![B 1 0,B 1 1;B 0 0,B 0 1]
def swapPlaneOrigin (c : Plane) : Plane := ![c 1,c 0]

theorem planeSwap_affine_image (B : PlaneMatrix) (c : Plane) (S : Set Plane) :
    planeSwap '' ((fun y => c+B*ᵥy) '' S)=
      (fun y => swapPlaneOrigin c+swapPlaneMatrix B*ᵥy) '' S := by
  rw [Set.image_image]
  apply Set.image_congr'
  intro y
  ext i
  fin_cases i <;>
    simp [swapPlaneOrigin,swapPlaneMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

def centralMatrix2 (p q r : ℝ) (i : Fin 3) : PlaneMatrix := ![
  stripMatrix (2*p) 0 0 (2*q),
  stripMatrix (2*r) (2*r) (-1) (2*(q+r)),
  swapPlaneMatrix (stripMatrix (2*r) (2*(q+r)) (-1) (2*(p+q+r)))] i

def centralOrigin2 (q r : ℝ) (i : Fin 3) : Plane := ![
  stripOrigin (2*r) 0 0,
  stripOrigin 0 (2*r) (-1),
  swapPlaneOrigin (stripOrigin (2*q) (2*(q+r)) (-1))] i

theorem centralRegion2_affine_square (p q r : ℝ) (hp : 0<p) (hq : 0<q)
    (hr : 0<r) (i : Fin 3) : centralRegion2 p q r i=
      (fun y => centralOrigin2 q r i+centralMatrix2 p q r i*ᵥy) '' planeUnitSquare := by
  fin_cases i
  · change _=(fun y => stripOrigin (2*r) 0 0+stripMatrix (2*p) 0 0 (2*q)*ᵥy) '' _
    rw [← equalSlopeTrapezoid_affine_square _ _ _ _ _ (by positivity) (by positivity)]
    ext x
    rw [Trapezoid.ofAffine_body _ _ _ _ _ _ (by positivity)]
    change (2*r≤x 0 ∧ x 0≤2*(p+r) ∧ 0≤x 1 ∧ x 1≤2*q) ↔ _
    simp only [zero_mul,add_zero,zero_add]
    constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> exact ⟨by linarith,by linarith,h3,h4⟩
  · change _=(fun y => stripOrigin 0 (2*r) (-1)+stripMatrix (2*r) (2*r) (-1) (2*(q+r))*ᵥy) '' _
    rw [← equalSlopeTrapezoid_affine_square _ _ _ _ _ (by positivity) (by linarith)]
    ext x
    rw [Trapezoid.ofAffine_body _ _ _ _ _ _ (by positivity)]
    change (0≤x 0 ∧ x 0≤2*r ∧ 2*r-x 0≤x 1 ∧ x 1≤2*(q+r)-x 0) ↔ _
    simp only [zero_add,neg_one_mul,sub_eq_add_neg]
  · change _=(fun y => swapPlaneOrigin (stripOrigin (2*q) (2*(q+r)) (-1))+
      swapPlaneMatrix (stripMatrix (2*r) (2*(q+r)) (-1) (2*(p+q+r)))*ᵥy) '' _
    rw [← planeSwap_affine_image,
      ← equalSlopeTrapezoid_affine_square _ _ _ _ _ (by positivity) (by linarith)]
    ext x
    have hs (S : Set Plane) : x∈planeSwap '' S ↔ planeSwap x∈S := by
      constructor
      · rintro ⟨y,hy,rfl⟩; simpa only [planeSwap_involutive] using hy
      · intro hx; exact ⟨planeSwap x,hx,planeSwap_involutive x⟩
    rw [hs,Trapezoid.ofAffine_body _ _ _ _ _ _ (by positivity)]
    change (2*q≤x 1 ∧ x 1≤2*(q+r) ∧ 2*(q+r)-x 1≤x 0 ∧ x 0≤2*(p+q+r)-x 1) ↔ _
    simp only [planeSwap_zero,planeSwap_one,neg_one_mul]
    constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;>
      exact ⟨h1,by linarith,by linarith,by linarith⟩

theorem centralMatrix2_det (p q r : ℝ) (i : Fin 3) :
    (centralMatrix2 p q r i).det=![4*p*q,4*r*q,-4*p*r] i := by
  fin_cases i <;>
    norm_num [centralMatrix2,stripMatrix,swapPlaneMatrix,Matrix.det_fin_two] <;> ring

theorem centralMatrix2_det_ne (p q r : ℝ) (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (i : Fin 3) : (centralMatrix2 p q r i).det≠0 := by
  rw [centralMatrix2_det]
  fin_cases i <;> simp [hp.ne',hq.ne',hr.ne']

def rectangularMatrix2 (p q η : ℝ) (i : Fin 4) : PlaneMatrix := ![
  !![η,0;0,2*q],!![2*p,0;0,η],!![η,0;0,2*q],!![2*p,0;0,η]] i
def rectangularOrigin2 (p q r η : ℝ) (i : Fin 4) : Plane := ![
  ![-η,2*r],![2*r,-η],![2*(p+r),0],![0,2*(q+r)]] i

theorem rectangularRegion2_affine_square (p q r η : ℝ) (hp : 0<p) (hq : 0<q)
    (hη : 0<η) (i : Fin 4) : localRegion2 p q r η (![1,2,4,5] i)=
      (fun y => rectangularOrigin2 p q r η i+rectangularMatrix2 p q η i*ᵥy) '' planeUnitSquare := by
  rw [rectangularRegion2_eq p q r η hp hη i]
  fin_cases i
  all_goals dsimp only [rectangularTrapezoid2,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
  all_goals rw [equalSlopeTrapezoid_affine_square _ _ _ _ _ (by positivity) (by linarith)]
  all_goals apply Set.image_congr'; intro y; ext j; fin_cases j <;>
    simp [rectangularOrigin2,rectangularMatrix2,stripOrigin,stripMatrix,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals try simp
  all_goals ring
  all_goals simp

theorem rectangularMatrix2_det_ne (p q η : ℝ) (hp : 0<p) (hq : 0<q) (hη : 0<η)
    (i : Fin 4) : (rectangularMatrix2 p q η i).det≠0 := by
  fin_cases i <;> simp [rectangularMatrix2,Matrix.det_fin_two,hp.ne',hq.ne',hη.ne']

end D4.C23Local
