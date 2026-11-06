import D4.PrincipalLaplacianCoordinates
import D4.PrincipalGraphIncidence

/-! The actual weighted Laplacian of K₅, with the article's ten edge weights. -/
noncomputable section
namespace D4.PrincipalSpectrum
open Matrix PrincipalGraphs

def fullIncidenceVector (e : Fin 10) : Fin 5 → ℝ := fun i =>
  (if edgeLo e=i then 1 else 0)-(if edgeHi e=i then 1 else 0)

def weightedLaplacian (w : Fin 10 → ℝ) : FullGram :=
  ∑ e, w e • Matrix.vecMulVec (fullIncidenceVector e) (fullIncidenceVector e)

private def integerLift : Matrix (Fin 5) (Fin 4) ℤ :=
  !![-1,-1,-1,-1;1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1]

private theorem integer_incidence_lift : ∀ (e : Fin 10) (i : Fin 5),
    ((if edgeLo e=i then 1 else 0)-(if edgeHi e=i then 1 else 0) : ℤ)=
      generatorSign e*∑ j,integerLift i j*Principal.integerGenerators e j := by decide +kernel

private theorem integerLift_cast (i : Fin 5) (j : Fin 4) :
    (integerLift i j : ℝ)=liftIncidence i j := by
  fin_cases i <;> fin_cases j <;> norm_num [integerLift,liftIncidence]

theorem fullIncidenceVector_lift (e : Fin 10) :
    fullIncidenceVector e=(generatorSign e : ℝ) • (liftIncidence*ᵥcone1Vectors e) := by
  ext i
  have h := congrArg (fun k : ℤ => (k : ℝ)) (integer_incidence_lift e i)
  simpa only [Int.cast_sub,Int.cast_mul,Int.cast_sum,Int.cast_ite,Int.cast_one,
    Int.cast_zero,integerLift_cast,Principal.generators_cast] using h

theorem lift_rankOne (v : Fin 4 → ℝ) :
    liftIncidence*rankOne v*liftIncidenceᵀ =
      Matrix.vecMulVec (liftIncidence*ᵥv) (liftIncidence*ᵥv) := by
  ext i j
  simp only [Matrix.mul_apply,rankOne,Matrix.transpose_apply,Matrix.vecMulVec_apply,
    Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem weightedLaplacian_eq_lifted (w : Fin 10 → ℝ) :
    weightedLaplacian w=liftedForm (principalForm w) := by
  unfold weightedLaplacian liftedForm principalForm
  rw [Matrix.mul_sum,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [Matrix.mul_smul,Matrix.smul_mul,lift_rankOne,fullIncidenceVector_lift]
  congr 1
  ext i j
  simp only [Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul]
  have hs : (generatorSign e : ℝ)^2=1 := by
    unfold generatorSign
    split_ifs <;> norm_num
  calc
    (generatorSign e : ℝ)*(liftIncidence*ᵥcone1Vectors e) i *
        ((generatorSign e : ℝ)*(liftIncidence*ᵥcone1Vectors e) j) =
        (generatorSign e : ℝ)^2*((liftIncidence*ᵥcone1Vectors e) i *
          (liftIncidence*ᵥcone1Vectors e) j) := by ring
    _ = _ := by rw [hs,one_mul]

theorem fullIncidenceVector_norm_sq (e : Fin 10) :
    ∑ i,fullIncidenceVector e i*fullIncidenceVector e i=2 := by
  have hterm (i : Fin 5) : fullIncidenceVector e i*fullIncidenceVector e i=
      (if i=edgeLo e then 1 else 0)+(if i=edgeHi e then 1 else 0) := by
    by_cases h1 : i=edgeLo e <;> by_cases h2 : i=edgeHi e
    · exact ((endpoints_distinct e) (h1.symm.trans h2)).elim
    all_goals simp [fullIncidenceVector,eq_comm,h1,h2,(endpoints_distinct e).symm]
  simp_rw [hterm]
  norm_num [Finset.sum_add_distrib]

theorem weightedLaplacian_trace (w : Fin 10 → ℝ) :
    (weightedLaplacian w).trace=2*∑ e,w e := by
  simp only [weightedLaplacian,Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul]
  simp only [Matrix.trace,Matrix.diag,Matrix.vecMulVec_apply,fullIncidenceVector_norm_sq]
  rw [← Finset.sum_mul]
  ring

theorem weightedLaplacian_entries (w : Fin 10 → ℝ) (i j : Fin 5) :
    weightedLaplacian w i j =
      ∑ e,w e*((if edgeLo e=i then 1 else 0)-(if edgeHi e=i then 1 else 0))*
        ((if edgeLo e=j then 1 else 0)-(if edgeHi e=j then 1 else 0)) := by
  simp only [weightedLaplacian,Matrix.sum_apply,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,
    Matrix.vecMulVec_apply,fullIncidenceVector,mul_assoc]

end D4.PrincipalSpectrum
