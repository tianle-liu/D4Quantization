import D4.C23LocalWindow
import D4.AreaTriangles
import D4.ParameterAffineIntegralAnalytic

/-! True four-dimensional affine charts for a moving polygonal window.
The quadratic form is independent of the form defining the window coordinates. -/
noncomputable section
namespace D4.C23Local
open Analytic AreaEnvelope Matrix MeasureTheory Set

def windowReference4 (S : Set Plane) (R : ℝ) : Set Vec :=
  splitCoordinates.symm '' referenceWindow S R

theorem windowReference4_compact (S : Set Plane) (hS : IsCompact S) (R : ℝ) :
    IsCompact (windowReference4 S R) := by
  apply (hS.prod (isCompact_Icc.prod isCompact_Icc)).image
  rw [show (splitCoordinates.symm : WindowCoordinates → Vec)=
    (fun p => ![p.2.1,p.2.2,p.1 0,p.1 1]) from funext splitCoordinates_symm_apply]
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : WindowCoordinates => p.2.1); fun_prop
  · change Continuous (fun p : WindowCoordinates => p.2.2); fun_prop
  · change Continuous (fun p : WindowCoordinates => p.1 0); fun_prop
  · change Continuous (fun p : WindowCoordinates => p.1 1); fun_prop

def windowAffineMatrix2 (B : PlaneMatrix) (u : Fin 3 → ℝ) : Gram :=
  !![-1,0,-(u 1*B 0 0+u 2*B 1 0),-(u 1*B 0 1+u 2*B 1 1);
     0,-1,-(u 1*B 0 0+u 2*B 1 0),-(u 1*B 0 1+u 2*B 1 1);
     0,0,B 0 0,B 0 1;
     0,0,B 1 0,B 1 1]

def windowAffineOrigin2 (Q : Gram) (c : Plane) (u : Fin 3 → ℝ) : Vec :=
  ![Q 0 0-affineEval u c,Q 1 1-affineEval u c,c 0-Q 2 2,c 1-Q 3 3]

theorem windowAffineMatrix2_det (B : PlaneMatrix) (u : Fin 3 → ℝ) :
    (windowAffineMatrix2 B u).det=B.det := by
  rw [Matrix.det_succ_row _ 0]
  norm_num [windowAffineMatrix2,Fin.sum_univ_succ,Matrix.det_fin_three,
    Matrix.det_fin_two]
  dsimp [Fin.succAbove,Fin.instOfNat,Fin.ofNat',Fin.lt_def,Fin.castSucc,
    Fin.succ,Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  norm_num
  ring

theorem windowPoint2_affine (Q : Gram) (B : PlaneMatrix) (c : Plane)
    (u : Fin 3 → ℝ) (p : WindowCoordinates) :
    windowPoint2 Q (affineEval u) (c+B*ᵥp.1,p.2)=
      windowAffineOrigin2 Q c u+windowAffineMatrix2 B u*ᵥsplitCoordinates.symm p := by
  rw [splitCoordinates_symm_apply]
  ext i
  fin_cases i <;>
    simp [windowPoint2,inverseCoordinates2,fiberCoordinates,windowAffineOrigin2,
      windowAffineMatrix2,affineEval_eq,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.cons_val] <;> ring

theorem localWindow2_affine_image (Q : Gram) (B : PlaneMatrix) (c : Plane)
    (u : Fin 3 → ℝ) (S : Set Plane) (R : ℝ) :
    localWindow2 Q (affineEval u) ((fun y => c+B*ᵥy) '' S) R=
      (fun x => windowAffineOrigin2 Q c u+windowAffineMatrix2 B u*ᵥx) ''
        windowReference4 S R := by
  ext x
  constructor
  · rintro ⟨⟨L,a,b⟩,⟨⟨y,hy,hL⟩,hab⟩,hx⟩
    change c+B*ᵥy=L at hL
    subst L
    refine ⟨splitCoordinates.symm (y,(a,b)),⟨(y,(a,b)),⟨hy,hab⟩,rfl⟩,?_⟩
    exact (windowPoint2_affine Q B c u (y,(a,b))).symm.trans hx
  · rintro ⟨v,⟨⟨y,a,b⟩,⟨hy,hab⟩,rfl⟩,hx⟩
    refine ⟨(c+B*ᵥy,(a,b)),⟨⟨y,hy,rfl⟩,hab⟩,?_⟩
    exact (windowPoint2_affine Q B c u (y,(a,b))).trans hx

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem localWindow2_affine_quadratic_analytic
    (S : Set Plane) (hS : IsCompact S) (R : ℝ)
    (Q H : P → Gram) (B : P → PlaneMatrix) (c : P → Plane)
    (u : P → Fin 3 → ℝ) (p₀ : P)
    (hQ : ∀ i j,AnalyticAt ℝ (fun p => Q p i j) p₀)
    (hH : ∀ i j,AnalyticAt ℝ (fun p => H p i j) p₀)
    (hB : ∀ i j,AnalyticAt ℝ (fun p => B p i j) p₀)
    (hc : ∀ i,AnalyticAt ℝ (fun p => c p i) p₀)
    (hu : ∀ i,AnalyticAt ℝ (fun p => u p i) p₀)
    (hdet : (B p₀).det≠0) :
    AnalyticAt ℝ (fun p => ∫ r in localWindow2 (Q p) (affineEval (u p))
      ((fun y => c p+B p*ᵥy) '' S) R,quadratic (H p) r) p₀ := by
  simp_rw [localWindow2_affine_image]
  apply ParameterAnalytic.integral_affineImage_quadratic
    (windowReference4 S R) (windowReference4_compact S hS R) H
    (fun p => windowAffineMatrix2 (B p) (u p))
    (fun p => windowAffineOrigin2 (Q p) (c p) (u p)) p₀ hH
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [windowAffineMatrix2,Matrix.cons_val]
    all_goals first
      | exact analyticAt_const
      | exact hB _ _
      | exact ((hu _).mul (hB _ _) |>.add ((hu _).mul (hB _ _))).neg
  · have he : AnalyticAt ℝ (fun p => affineEval (u p) (c p)) p₀ := by
      simp only [affineEval_eq]
      exact ((hu 0).add ((hu 1).mul (hc 0))).add ((hu 2).mul (hc 1))
    intro i
    fin_cases i <;> simp only [windowAffineOrigin2,Matrix.cons_val]
    · exact (hQ 0 0).sub he
    · exact (hQ 1 1).sub he
    · exact (hc 0).sub (hQ 2 2)
    · exact (hc 1).sub (hQ 3 3)
  · simpa only [windowAffineMatrix2_det] using hdet

end D4.C23Local
