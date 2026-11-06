import D4.PrincipalCircuits

/-! The checked dependence is the fundamental circuit: every relation on a
 tree plus one extra column is its scalar multiple, with the same nonzero support. -/
namespace D4.Principal
open Matrix Analytic

theorem fundamentalCircuit_relation_unique (t : Fin 125) (e : Fin 10) (c : Fin 5 → ℤ)
    (hc : ∑ j,c j • fundamentalCircuitColumns t e j=0) :
    ∀ j,c j=c 0*fundamentalCircuitCoefficients t e j := by
  have hA : integerTreeMatrix t *ᵥ (fun j => c j.succ)=(-c 0) • integerGenerators e := by
    ext i
    have h := congrFun hc i
    rw [Finset.sum_apply,Fin.sum_univ_succ] at h
    simp only [fundamentalCircuitColumns,Fin.cons_zero,Fin.cons_succ,
      Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at h
    change (∑ j,integerGenerators (treeEdges t j) i*c j.succ)=(-c 0)*integerGenerators e i
    simp_rw [mul_comm (integerGenerators _ i)]
    linarith
  have h := congrArg (fun v => treeInverse t *ᵥ v) hA
  dsimp only at h
  rw [Matrix.mulVec_mulVec,tree_inverse_mul,Matrix.one_mulVec,Matrix.mulVec_smul] at h
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · change c 0=c 0*1
    ring
  · have hk := congrFun h k
    change c k.succ=(-c 0)*treeCoordinates t e k at hk
    change c k.succ=c 0*(-treeCoordinates t e k)
    linarith

theorem fundamentalCircuit_minimal_support (t : Fin 125) (e : Fin 10) (c : Fin 5 → ℤ)
    (hc : ∑ j,c j • fundamentalCircuitColumns t e j=0) (hne : c≠0) :
    ∀ j,c j≠0 ↔ fundamentalCircuitCoefficients t e j≠0 := by
  have h := fundamentalCircuit_relation_unique t e c hc
  have h0 : c 0≠0 := by
    intro he
    apply hne
    ext j
    rw [h j,he,zero_mul]
    rfl
  intro j
  rw [h j,mul_ne_zero_iff,and_iff_right h0]

end D4.Principal
