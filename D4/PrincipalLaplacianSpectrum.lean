import D4.PrincipalLaplacian

/-! The four positive eigenvalues of the full five-vertex weighted Laplacian,
including an orthonormal spectral decomposition and exhaustion of its nonzero spectrum. -/
noncomputable section
namespace D4.PrincipalSpectrum
open Matrix

def positiveEigenvalues (Q : RealGram) (hQ : Q.PosDef) : Fin 4 → ℝ :=
  (compressedForm_posDef hQ).isHermitian.eigenvalues

def spectralColumns (Q : RealGram) (hQ : Q.PosDef) : LiftMatrix :=
  orthogonalLift*((compressedForm_posDef hQ).isHermitian.eigenvectorUnitary : RealGram)

theorem spectralColumns_gram (Q : RealGram) (hQ : Q.PosDef) :
    (spectralColumns Q hQ)ᵀ*spectralColumns Q hQ=1 := by
  unfold spectralColumns
  rw [Matrix.transpose_mul]
  calc
    _ = ((compressedForm_posDef hQ).isHermitian.eigenvectorUnitary : RealGram)ᵀ*
      (orthogonalLiftᵀ*orthogonalLift)*
      ((compressedForm_posDef hQ).isHermitian.eigenvectorUnitary : RealGram) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [orthogonalLift_gram,Matrix.mul_one]
      simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using
        unitary.coe_star_mul_self (compressedForm_posDef hQ).isHermitian.eigenvectorUnitary

theorem lifted_spectral_decomposition (Q : RealGram) (hQ : Q.PosDef) :
    liftedForm Q=spectralColumns Q hQ*Matrix.diagonal (positiveEigenvalues Q hQ)*
      (spectralColumns Q hQ)ᵀ := by
  have hs := (compressedForm_posDef hQ).isHermitian.spectral_theorem
  simp only [Function.comp_def,RCLike.ofReal_real_eq_id, id_eq,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at hs
  rw [liftedForm_eq_compressed,hs]
  simp only [spectralColumns,positiveEigenvalues,Matrix.transpose_mul,Matrix.mul_assoc]

theorem positiveEigenvalues_pos (Q : RealGram) (hQ : Q.PosDef) (i : Fin 4) :
    0<positiveEigenvalues Q hQ i := (compressedForm_posDef hQ).eigenvalues_pos i

theorem positiveEigenvalues_prod (Q : RealGram) (hQ : Q.PosDef) :
    ∏ i,positiveEigenvalues Q hQ i=5*Q.det := by
  have h := (compressedForm_posDef hQ).isHermitian.det_eq_prod_eigenvalues
  simpa only [positiveEigenvalues,compressedForm_det,RCLike.ofReal_real_eq_id, id_eq] using h.symm

theorem positiveEigenvalues_sum (Q : RealGram) (hQ : Q.PosDef) :
    ∑ i,positiveEigenvalues Q hQ i=(liftedForm Q).trace := by
  rw [← compressedForm_trace,trace_eq_sum_eigenvalues (compressedForm_posDef hQ).isHermitian]
  rfl

theorem spectral_column_nonzero {U : LiftMatrix} (hU : Uᵀ*U=1) (j : Fin 4) :
    U*ᵥPi.single j 1 ≠ 0 := by
  intro hz
  have h := congrArg (fun x => Uᵀ*ᵥx) hz
  dsimp only at h
  rw [Matrix.mulVec_mulVec,hU,Matrix.one_mulVec,Matrix.mulVec_zero] at h
  have hj := congrFun h j
  simpa using hj

theorem spectral_column_eigenvector {A : FullGram} {U : LiftMatrix} {ρ : Fin 4 → ℝ}
    (hU : Uᵀ*U=1) (hA : A=U*Matrix.diagonal ρ*Uᵀ) (j : Fin 4) :
    A*ᵥ(U*ᵥPi.single j 1)=ρ j • (U*ᵥPi.single j 1) := by
  have hd : Matrix.diagonal ρ*ᵥPi.single j 1=ρ j • (Pi.single j (1 : ℝ) : Fin 4 → ℝ) := by
    ext i
    by_cases hij : i=j <;> simp [Matrix.mulVec_diagonal,hij,Pi.single_apply]
  calc
    _ = U*ᵥ(Matrix.diagonal ρ*ᵥ((Uᵀ*U)*ᵥPi.single j 1)) := by
      rw [hA]
      simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]
    _ = _ := by rw [hU,Matrix.one_mulVec,hd,Matrix.mulVec_smul]

theorem spectral_nonzero_exhaustive {A : FullGram} {U : LiftMatrix} {ρ : Fin 4 → ℝ}
    (hU : Uᵀ*U=1) (hA : A=U*Matrix.diagonal ρ*Uᵀ)
    {μ : ℝ} (hμ : μ≠0) {x : Fin 5 → ℝ} (hx : x≠0) (he : A*ᵥx=μ • x) :
    ∃ i,μ=ρ i := by
  have hy : Uᵀ*ᵥx≠0 := by
    intro hy
    have hz : μ • x=0 := by
      rw [← he,hA]
      simp only [← Matrix.mulVec_mulVec,hy,Matrix.mulVec_zero]
    exact (smul_eq_zero.mp hz).elim hμ hx
  have hUA : Uᵀ*A=Matrix.diagonal ρ*Uᵀ := by
    rw [hA]
    calc
      _ = (Uᵀ*U)*(Matrix.diagonal ρ*Uᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU,Matrix.one_mul]
  have hd : Matrix.diagonal ρ*ᵥ(Uᵀ*ᵥx)=μ • (Uᵀ*ᵥx) := by
    have hh := congrArg (fun v => Uᵀ*ᵥv) he
    dsimp only at hh
    rw [Matrix.mulVec_mulVec,hUA,Matrix.mulVec_smul] at hh
    simpa only [Matrix.mulVec_mulVec] using hh
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hy
  have hdi := congrFun hd i
  simp only [Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul] at hdi
  exact ⟨i,(mul_right_cancel₀ hi hdi).symm⟩

/-- The original five-dimensional Laplacian has precisely the displayed four
positive eigenvalues, counted by its four orthonormal eigenvectors. -/
theorem principal_laplacian_nonzero_spectrum (w : Fin 10 → ℝ)
    (hQ : (principalForm w).PosDef) :
    ∃ (ρ : Fin 4 → ℝ) (U : LiftMatrix),
      Uᵀ*U=1 ∧ weightedLaplacian w=U*Matrix.diagonal ρ*Uᵀ ∧
      (∀ i,0<ρ i) ∧ (∏ i,ρ i)=5*(principalForm w).det ∧ (∑ i,ρ i)=2*∑ e,w e ∧
      (∀ i,U*ᵥPi.single i 1≠0 ∧
        weightedLaplacian w*ᵥ(U*ᵥPi.single i 1)=ρ i • (U*ᵥPi.single i 1)) ∧
      (∀ (μ : ℝ) (x : Fin 5 → ℝ),μ≠0 → x≠0 →
        weightedLaplacian w*ᵥx=μ • x → ∃ i,μ=ρ i) := by
  let ρ := positiveEigenvalues (principalForm w) hQ
  let U := spectralColumns (principalForm w) hQ
  have hU : Uᵀ*U=1 := spectralColumns_gram _ hQ
  have hA : weightedLaplacian w=U*Matrix.diagonal ρ*Uᵀ := by
    rw [weightedLaplacian_eq_lifted]
    exact lifted_spectral_decomposition _ hQ
  refine ⟨ρ,U,hU,hA,positiveEigenvalues_pos _ hQ,positiveEigenvalues_prod _ hQ,?_,?_,?_⟩
  · rw [positiveEigenvalues_sum,← weightedLaplacian_eq_lifted,weightedLaplacian_trace]
  · intro i
    exact ⟨spectral_column_nonzero hU i,spectral_column_eigenvector hU hA i⟩
  · intro μ x hμ hx he
    exact spectral_nonzero_exhaustive hU hA hμ hx he

end D4.PrincipalSpectrum
