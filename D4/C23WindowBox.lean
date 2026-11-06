import D4.C23WindowMeasure
import D4.ParameterParallelotopeAnalytic

/-! An affine rectangular local window is an actual four-dimensional parallelotope. -/
noncomputable section
namespace D4.C23Local
open Matrix MeasureTheory Set Analytic AreaEnvelope Principal

def rectangleLower (u : Fin 3 → ℝ) (L : Plane) : ℝ := u 0+u 1*L 0+u 2*L 1

def rectangleMatrix (lo hi : Plane) (R : ℝ) (u : Fin 3 → ℝ) : Gram :=
  !![(hi 0-lo 0)/2,0,0,0;
     0,(hi 1-lo 1)/2,0,0;
     -u 1*((hi 0-lo 0)/2),-u 2*((hi 1-lo 1)/2),-R,0;
     -u 1*((hi 0-lo 0)/2),-u 2*((hi 1-lo 1)/2),0,-R]

def rectangleCenter (Q : Gram) (lo hi : Plane) (u : Fin 3 → ℝ) : Vec :=
  ![(hi 0+lo 0)/2-Q 0 0,(hi 1+lo 1)/2-Q 1 1,
    Q 2 2-u 0-u 1*((hi 0+lo 0)/2)-u 2*((hi 1+lo 1)/2),
    Q 3 3-u 0-u 1*((hi 0+lo 0)/2)-u 2*((hi 1+lo 1)/2)]

def rectangleCoordinates (lo hi : Plane) (R : ℝ) (x : Vec) : WindowCoordinates :=
  (![(hi 0+lo 0)/2+(hi 0-lo 0)/2*x 0,
     (hi 1+lo 1)/2+(hi 1-lo 1)/2*x 1],(R*x 2,R*x 3))

theorem rectangleCoordinates_point (Q : Gram) (lo hi : Plane) (R : ℝ)
    (u : Fin 3 → ℝ) (x : Vec) :
    windowPoint3 Q (rectangleLower u) (rectangleCoordinates lo hi R x)=
      rectangleCenter Q lo hi u+rectangleMatrix lo hi R u *ᵥ x := by
  ext i
  fin_cases i <;>
    simp [windowPoint3,inverseCoordinates3,fiberCoordinates,rectangleLower,
      rectangleCoordinates,rectangleCenter,rectangleMatrix,Matrix.mulVec,dotProduct,
      Fin.sum_univ_four] <;> ring

theorem interval_midpoint_bounds {a b t : ℝ} (hab : a≤b) (ht : t∈Icc (-1:ℝ) 1) :
    (b+a)/2+(b-a)/2*t∈Icc a b := by
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ht.2),
    mul_nonneg (sub_nonneg.mpr hab) (by linarith [ht.1] : 0≤t+1)]

theorem interval_midpoint_surjective {a b y : ℝ} (hab : a<b) (hy : y∈Icc a b) :
    ∃t∈Icc (-1:ℝ) 1,y=(b+a)/2+(b-a)/2*t := by
  refine ⟨(2*y-a-b)/(b-a),?_,?_⟩
  · constructor
    · apply (le_div_iff₀ (sub_pos.mpr hab)).2
      linarith [hy.1]
    · apply (div_le_iff₀ (sub_pos.mpr hab)).2
      linarith [hy.2]
  · field_simp [sub_ne_zero.mpr hab.ne']
    <;> ring

theorem rectangleCoordinates_image (lo hi : Plane) (R : ℝ)
    (hlo : ∀i,lo i<hi i) (hR : 0<R) :
    rectangleCoordinates lo hi R '' Principal.centeredCube = referenceWindow (Icc lo hi) R := by
  ext p
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hx' : ∀i,x i∈Icc (-1:ℝ) 1 := fun i => ⟨hx.1 i,hx.2 i⟩
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · intro i; fin_cases i
      · exact (interval_midpoint_bounds (hlo 0).le (hx' 0)).1
      · exact (interval_midpoint_bounds (hlo 1).le (hx' 1)).1
    · intro i; fin_cases i
      · exact (interval_midpoint_bounds (hlo 0).le (hx' 0)).2
      · exact (interval_midpoint_bounds (hlo 1).le (hx' 1)).2
    · change -R≤R*x 2 ∧ R*x 2≤R
      constructor <;> nlinarith [(hx' 2).1,(hx' 2).2]
    · change -R≤R*x 3 ∧ R*x 3≤R
      constructor <;> nlinarith [(hx' 3).1,(hx' 3).2]
  · rintro ⟨hp,hs,ht⟩
    obtain ⟨x0,h0,e0⟩ := interval_midpoint_surjective (hlo 0) ⟨hp.1 0,hp.2 0⟩
    obtain ⟨x1,h1,e1⟩ := interval_midpoint_surjective (hlo 1) ⟨hp.1 1,hp.2 1⟩
    refine ⟨![x0,x1,p.2.1/R,p.2.2/R],?_,?_⟩
    · constructor <;> intro i <;> fin_cases i <;> simp only [Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Pi.neg_apply,Pi.one_apply]
      · exact h0.1
      · exact h1.1
      · exact (le_div_iff₀ hR).2 (by nlinarith [hs.1])
      · exact (le_div_iff₀ hR).2 (by nlinarith [ht.1])
      · exact h0.2
      · exact h1.2
      · exact (div_le_iff₀ hR).2 (by nlinarith [hs.2])
      · exact (div_le_iff₀ hR).2 (by nlinarith [ht.2])
    · apply Prod.ext
      · ext i; fin_cases i <;> simp [rectangleCoordinates,←e0,←e1]
      · apply Prod.ext <;> simp [rectangleCoordinates,mul_div_cancel₀ _ hR.ne']

theorem localWindow3_rectangle_parallelotope (Q : Gram) (lo hi : Plane) (R : ℝ)
    (u : Fin 3 → ℝ) (hlo : ∀i,lo i<hi i) (hR : 0<R) :
    localWindow3 Q (rectangleLower u) (Icc lo hi) R =
      parallelotope (rectangleMatrix lo hi R u) (rectangleCenter Q lo hi u) := by
  unfold localWindow3
  rw [←rectangleCoordinates_image lo hi R hlo hR,Set.image_image]
  simp only [Function.comp_def,rectangleCoordinates_point,parallelotope]

theorem rectangleMatrix_det (lo hi : Plane) (R : ℝ) (u : Fin 3 → ℝ) :
    (rectangleMatrix lo hi R u).det=(hi 0-lo 0)*(hi 1-lo 1)*R^2/4 := by
  have ht : (rectangleMatrix lo hi R u).BlockTriangular
      (OrderDual.toDual : Fin 4 → (Fin 4)ᵒᵈ) := by
    intro i j hij
    change i<j at hij
    fin_cases i <;> fin_cases j <;> norm_num [rectangleMatrix] at hij ⊢
  rw [Matrix.det_of_lowerTriangular _ ht]
  simp [rectangleMatrix,Fin.prod_univ_four]
  ring

end D4.C23Local
