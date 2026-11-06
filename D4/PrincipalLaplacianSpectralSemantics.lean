import D4.PrincipalLaplacianSpectrum
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Standard eigenspace semantics and multiplicities for the Laplacian spectrum. -/
noncomputable section
namespace D4.PrincipalSpectrum
open Matrix

theorem weightedLaplacian_hasEigenvalue_iff (w : Fin 10 → ℝ)
    (hQ : (principalForm w).PosDef) (μ : ℝ) (hμ : μ≠0) :
    Module.End.HasEigenvalue (Matrix.toLin' (weightedLaplacian w)) μ ↔
      μ∈Set.range (positiveEigenvalues (principalForm w) hQ) := by
  let U := spectralColumns (principalForm w) hQ
  have hU : Uᵀ*U=1 := spectralColumns_gram _ hQ
  have hA : weightedLaplacian w=U*diagonal (positiveEigenvalues _ hQ)*Uᵀ := by
    rw [weightedLaplacian_eq_lifted]
    exact lifted_spectral_decomposition _ hQ
  constructor
  · intro h
    obtain ⟨x,hx⟩ := h.exists_hasEigenvector
    have he : weightedLaplacian w*ᵥx=μ • x := hx.apply_eq_smul
    obtain ⟨i,hi⟩ := spectral_nonzero_exhaustive hU hA hμ hx.2 he
    exact ⟨i,hi.symm⟩
  · rintro ⟨i,rfl⟩
    apply Module.End.HasUnifEigenvector.hasUnifEigenvalue
    apply Module.End.hasEigenvector_iff.mpr
    refine ⟨?_,spectral_column_nonzero hU i⟩
    rw [Module.End.mem_eigenspace_iff,Matrix.toLin'_apply]
    exact spectral_column_eigenvector hU hA i

theorem spectral_det_one_add {A : FullGram} {U : LiftMatrix} {ρ : Fin 4 → ℝ}
    (hU : Uᵀ*U=1) (hA : A=U*diagonal ρ*Uᵀ) (t : ℝ) :
    ((1 : FullGram)+t • A).det=∏ i : Fin 4,(1+t*ρ i) := by
  have he : (1 : FullGram)+t • A=1+U*(t • diagonal ρ*Uᵀ) := by
    rw [hA]
    simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]
  rw [he,Matrix.det_one_add_mul_comm]
  have hm : (t • diagonal ρ*Uᵀ)*U=t • diagonal ρ := by
    rw [Matrix.mul_assoc,hU,Matrix.mul_one]
  rw [hm]
  have hd : (1 : RealGram)+t • diagonal ρ=diagonal (fun i => 1+t*ρ i) := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal,Matrix.one_apply,hij]
  rw [hd,Matrix.det_diagonal]

/-- This determinant identity includes the algebraic multiplicities of all
four positive eigenvalues; the fifth eigenvalue is zero. -/
theorem weightedLaplacian_det_one_add (w : Fin 10 → ℝ)
    (hQ : (principalForm w).PosDef) (t : ℝ) :
    ((1 : FullGram)+t • weightedLaplacian w).det=
      ∏ i : Fin 4,(1+t*positiveEigenvalues (principalForm w) hQ i) := by
  apply spectral_det_one_add (spectralColumns_gram _ hQ)
  rw [weightedLaplacian_eq_lifted]
  exact lifted_spectral_decomposition _ hQ

theorem liftIncidence_mulVec_injective : Function.Injective liftIncidence.mulVec := by
  intro x y h
  ext i
  have hi := congrFun h i.succ
  fin_cases i <;>
    simpa [liftIncidence,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hi

theorem liftIncidence_transpose_mulVec (x : Fin 5 → ℝ) :
    liftIncidenceᵀ*ᵥx=![x 1-x 0,x 2-x 0,x 3-x 0,x 4-x 0] := by
  ext i
  fin_cases i <;>
    simp [liftIncidence,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem weightedLaplacian_kernel (w : Fin 10 → ℝ)
    (hQ : (principalForm w).PosDef) (x : Fin 5 → ℝ) :
    weightedLaplacian w*ᵥx=0 ↔ ∃ c : ℝ,x=fun _ => c := by
  have hQI : Function.Injective (principalForm w).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hQ.det_pos.ne'))
  constructor
  · intro h
    rw [weightedLaplacian_eq_lifted,liftedForm] at h
    have hE : liftIncidence*ᵥ((principalForm w)*ᵥ(liftIncidenceᵀ*ᵥx))=
        liftIncidence*ᵥ0 := by
      simpa only [Matrix.mulVec_mulVec,Matrix.mulVec_zero,Matrix.mul_assoc] using h
    have hQ0 := liftIncidence_mulVec_injective hE
    have hz : liftIncidenceᵀ*ᵥx=0 := hQI (hQ0.trans (Matrix.mulVec_zero _).symm)
    rw [liftIncidence_transpose_mulVec] at hz
    refine ⟨x 0,?_⟩
    ext i
    fin_cases i
    · rfl
    · have hh := congrFun hz 0
      simpa using sub_eq_zero.mp hh
    · have hh := congrFun hz 1
      simpa using sub_eq_zero.mp hh
    · have hh := congrFun hz 2
      simpa using sub_eq_zero.mp hh
    · have hh := congrFun hz 3
      simpa using sub_eq_zero.mp hh
  · rintro ⟨c,rfl⟩
    rw [weightedLaplacian_eq_lifted,liftedForm]
    simp only [← Matrix.mulVec_mulVec,liftIncidence_transpose_mulVec,sub_self]
    have hz : (![0,0,0,0] : Fin 4 → ℝ)=0 := by ext i; fin_cases i <;> rfl
    rw [hz,Matrix.mulVec_zero,Matrix.mulVec_zero]

end D4.PrincipalSpectrum
