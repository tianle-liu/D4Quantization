import D4.Determinant

/-! Orthogonal coordinates for the nonconstant part of the five-vertex
weighted Laplacian. -/
noncomputable section
namespace D4.PrincipalSpectrum
open Matrix

abbrev FullGram := Matrix (Fin 5) (Fin 5) ℝ
abbrev LiftMatrix := Matrix (Fin 5) (Fin 4) ℝ

def liftIncidence : LiftMatrix :=
  !![-1,-1,-1,-1;1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1]

def coupling : RealGram := !![2,1,1,1;1,2,1,1;1,1,2,1;1,1,1,2]

def squareRoot : RealGram :=
  let c := (Real.sqrt 5-1)/4
  !![1+c,c,c,c;c,1+c,c,c;c,c,1+c,c;c,c,c,1+c]

theorem liftIncidence_gram : liftIncidenceᵀ*liftIncidence=coupling := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [liftIncidence,coupling,Matrix.mul_apply,Fin.sum_univ_succ]

theorem squareRoot_transpose : squareRootᵀ=squareRoot := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem squareRoot_square : squareRoot*squareRoot=coupling := by
  have hs : Real.sqrt 5 ^ 2=5 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [squareRoot,coupling,Matrix.mul_apply,Fin.sum_univ_succ] <;> nlinarith

theorem coupling_det : coupling.det=5 := by
  let G : Matrix (Fin 4) (Fin 4) ℤ := !![2,1,1,1;1,2,1,1;1,1,2,1;1,1,1,2]
  have hdet : G.det=5 := by decide
  have hmap : G.map (Int.castRingHom ℝ)=coupling := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [G,coupling]
  rw [← hmap]
  change (G.map (fun x : ℤ => (x : ℝ))).det=5
  rw [← Int.cast_det,hdet]
  norm_num

theorem squareRoot_det_sq : squareRoot.det^2=5 := by
  have h := congrArg Matrix.det squareRoot_square
  rw [Matrix.det_mul,coupling_det] at h
  nlinarith only [h]

theorem squareRoot_det_unit : IsUnit squareRoot.det := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  have := squareRoot_det_sq
  rw [h] at this
  norm_num at this

theorem squareRoot_inv_transpose : squareRoot⁻¹ᵀ=squareRoot⁻¹ := by
  rw [Matrix.transpose_nonsing_inv,squareRoot_transpose]

def orthogonalLift : LiftMatrix := liftIncidence*squareRoot⁻¹

theorem orthogonalLift_gram : orthogonalLiftᵀ*orthogonalLift=1 := by
  unfold orthogonalLift
  rw [Matrix.transpose_mul,squareRoot_inv_transpose]
  calc
    squareRoot⁻¹*liftIncidenceᵀ*(liftIncidence*squareRoot⁻¹) =
        squareRoot⁻¹*(liftIncidenceᵀ*liftIncidence)*squareRoot⁻¹ := by simp only [Matrix.mul_assoc]
    _ = squareRoot⁻¹*(squareRoot*squareRoot)*squareRoot⁻¹ := by
      rw [liftIncidence_gram,squareRoot_square]
    _ = 1 := by simp [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ squareRoot_det_unit,
      Matrix.mul_nonsing_inv _ squareRoot_det_unit]

theorem orthogonalLift_mul_squareRoot : orthogonalLift*squareRoot=liftIncidence := by
  simp [orthogonalLift,Matrix.mul_assoc,Matrix.nonsing_inv_mul _ squareRoot_det_unit]

def liftedForm (Q : RealGram) : FullGram := liftIncidence*Q*liftIncidenceᵀ

def compressedForm (Q : RealGram) : RealGram := squareRoot*Q*squareRoot

theorem compressedForm_posDef {Q : RealGram} (hQ : Q.PosDef) : (compressedForm Q).PosDef := by
  have hi : Function.Injective squareRoot.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr squareRoot_det_unit)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,squareRoot_transpose] using
    hQ.conjTranspose_mul_mul_same hi

theorem compressedForm_det (Q : RealGram) : (compressedForm Q).det=5*Q.det := by
  simp only [compressedForm,Matrix.det_mul]
  calc
    squareRoot.det*Q.det*squareRoot.det = squareRoot.det^2*Q.det := by ring
    _ = 5*Q.det := by rw [squareRoot_det_sq]

theorem liftedForm_eq_compressed (Q : RealGram) :
    liftedForm Q=orthogonalLift*compressedForm Q*orthogonalLiftᵀ := by
  have ht := congrArg Matrix.transpose orthogonalLift_mul_squareRoot
  rw [Matrix.transpose_mul,squareRoot_transpose] at ht
  unfold liftedForm compressedForm
  rw [← orthogonalLift_mul_squareRoot]
  simp only [Matrix.transpose_mul,squareRoot_transpose,Matrix.mul_assoc]

theorem compressedForm_trace (Q : RealGram) : (compressedForm Q).trace=(liftedForm Q).trace := by
  rw [liftedForm_eq_compressed,Matrix.trace_mul_cycle,orthogonalLift_gram,Matrix.one_mul]

end D4.PrincipalSpectrum
