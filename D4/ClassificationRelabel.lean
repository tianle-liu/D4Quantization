import D4.ClassificationDefs

/-! Permuting a superbase is an actual unimodular integer basis change. -/
namespace D4.Classification
open Matrix Analytic

/-- The columns are the relabelled four independent superbase vectors. -/
def relabelMatrix (σ : Equiv.Perm (Fin 5)) : IntegerMatrix :=
  fun r c => superVector (σ c.succ) r

theorem relabel_mulVec (σ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    relabelMatrix σ *ᵥ superVector i = superVector (σ i) := by
  ext r
  have hzero : ∑ j : Fin 5, superVector j r = 0 := by
    fin_cases r <;> norm_num [superVector, Fin.sum_univ_succ]
  have hsum : ∑ j : Fin 5, superVector (σ j) r = 0 := by
    exact (Equiv.sum_comp σ (fun j => superVector j r)).trans hzero
  fin_cases i
  · have h0 : superVector 0 = fun _ => -1 := by
      ext j
      fin_cases j <;> rfl
    change (relabelMatrix σ *ᵥ superVector 0) r = superVector (σ 0) r
    rw [h0]
    simp only [relabelMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      mul_neg, mul_one, Fin.sum_univ_zero, add_zero]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
    linarith
  all_goals simp [relabelMatrix, superVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem relabel_mul (σ τ : Equiv.Perm (Fin 5)) :
    relabelMatrix σ * relabelMatrix τ = relabelMatrix (τ.trans σ) := by
  ext r c
  change (relabelMatrix σ *ᵥ superVector (τ c.succ)) r = _
  rw [relabel_mulVec]
  rfl

theorem relabel_one : relabelMatrix (Equiv.refl (Fin 5)) = 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;> rfl

theorem relabel_mul_symm (σ : Equiv.Perm (Fin 5)) :
    relabelMatrix σ * relabelMatrix σ.symm = 1 := by
  rw [relabel_mul]
  simpa using relabel_one


theorem relabel_isUnit_det (σ : Equiv.Perm (Fin 5)) :
    IsUnit (relabelMatrix σ).det := by
  apply isUnit_of_mul_eq_one _ (relabelMatrix σ.symm).det
  rw [← Matrix.det_mul, relabel_mul_symm, Matrix.det_one]


noncomputable section

theorem superInner_relabel (Q : RealGram) (σ : Equiv.Perm (Fin 5)) (i j : Fin 5) :
    superInner (transform Q (relabelMatrix σ)) i j = superInner Q (σ i) (σ j) := by
  unfold superInner transform
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [← castVec_mulVec, ← castVec_mulVec, relabel_mulVec, relabel_mulVec]

theorem energy_relabel (Q : RealGram) (σ : Equiv.Perm (Fin 5)) :
    energy (transform Q (relabelMatrix σ)) = energy Q := by
  unfold energy transform
  simp_rw [quadratic_congruence, ← castVec_mulVec, relabel_mulVec]
  exact Equiv.sum_comp σ (fun i => quadratic Q (castVec (superVector i)))

theorem pairReduced_relabel {Q : RealGram} (hQ : PairReduced Q)
    (σ : Equiv.Perm (Fin 5)) : PairReduced (transform Q (relabelMatrix σ)) := by
  intro i j k hij hik hjk
  simpa only [superInner_relabel] using
    hQ (σ i) (σ j) (σ k) (σ.injective.ne hij) (σ.injective.ne hik) (σ.injective.ne hjk)

theorem relabel_integralCongruent (Q : RealGram) (σ : Equiv.Perm (Fin 5)) :
    IntegralCongruent Q (transform Q (relabelMatrix σ)) :=
  ⟨relabelMatrix σ, relabel_isUnit_det σ, rfl⟩

end
end D4.Classification
