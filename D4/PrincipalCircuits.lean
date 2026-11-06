import D4.PrincipalTreeCertificates

/-! Fundamental dependence coefficients of the actual reduced incidence
columns. The checked coordinates are the unique coordinates in each tree basis. -/
namespace D4.Principal
open Matrix Analytic

 def treeCoordinates (t : Fin 125) (e : Fin 10) : Fin 4 → ℤ :=
  treeInverse t *ᵥ integerGenerators e

 def circuitCoefficientCheck (t : Fin 125) : Bool :=
  (List.finRange 10).all fun e => (List.finRange 4).all fun j =>
    decide (treeCoordinates t e j=0 ∨ treeCoordinates t e j=1 ∨ treeCoordinates t e j = -1)

theorem circuit_coefficients_0 : ([0,1,2,3,4] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_1 : ([5,6,7,8,9] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_2 : ([10,11,12,13,14] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_3 : ([15,16,17,18,19] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_4 : ([20,21,22,23,24] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_5 : ([25,26,27,28,29] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_6 : ([30,31,32,33,34] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_7 : ([35,36,37,38,39] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_8 : ([40,41,42,43,44] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_9 : ([45,46,47,48,49] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_10 : ([50,51,52,53,54] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_11 : ([55,56,57,58,59] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_12 : ([60,61,62,63,64] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_13 : ([65,66,67,68,69] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_14 : ([70,71,72,73,74] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_15 : ([75,76,77,78,79] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_16 : ([80,81,82,83,84] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_17 : ([85,86,87,88,89] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_18 : ([90,91,92,93,94] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_19 : ([95,96,97,98,99] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_20 : ([100,101,102,103,104] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_21 : ([105,106,107,108,109] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_22 : ([110,111,112,113,114] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_23 : ([115,116,117,118,119] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl
theorem circuit_coefficients_24 : ([120,121,122,123,124] : List (Fin 125)).all circuitCoefficientCheck=true := by kernel_rfl

theorem treeCoordinates_zero_one_neg (t : Fin 125) (e : Fin 10) (j : Fin 4) :
    treeCoordinates t e j=0 ∨ treeCoordinates t e j=1 ∨ treeCoordinates t e j = -1 := by
  have hall : (List.finRange 125).all circuitCoefficientCheck=true := by
    have he : List.finRange 125 = ([0,1,2,3,4] : List (Fin 125)) ++ ([5,6,7,8,9] : List (Fin 125)) ++ ([10,11,12,13,14] : List (Fin 125)) ++ ([15,16,17,18,19] : List (Fin 125)) ++ ([20,21,22,23,24] : List (Fin 125)) ++ ([25,26,27,28,29] : List (Fin 125)) ++ ([30,31,32,33,34] : List (Fin 125)) ++ ([35,36,37,38,39] : List (Fin 125)) ++ ([40,41,42,43,44] : List (Fin 125)) ++ ([45,46,47,48,49] : List (Fin 125)) ++ ([50,51,52,53,54] : List (Fin 125)) ++ ([55,56,57,58,59] : List (Fin 125)) ++ ([60,61,62,63,64] : List (Fin 125)) ++ ([65,66,67,68,69] : List (Fin 125)) ++ ([70,71,72,73,74] : List (Fin 125)) ++ ([75,76,77,78,79] : List (Fin 125)) ++ ([80,81,82,83,84] : List (Fin 125)) ++ ([85,86,87,88,89] : List (Fin 125)) ++ ([90,91,92,93,94] : List (Fin 125)) ++ ([95,96,97,98,99] : List (Fin 125)) ++ ([100,101,102,103,104] : List (Fin 125)) ++ ([105,106,107,108,109] : List (Fin 125)) ++ ([110,111,112,113,114] : List (Fin 125)) ++ ([115,116,117,118,119] : List (Fin 125)) ++ ([120,121,122,123,124] : List (Fin 125)) := by kernel_rfl
    rw [he]
    simp (config := {implicitDefEqProofs := false}) only [List.all_append,
      circuit_coefficients_0, circuit_coefficients_1, circuit_coefficients_2, circuit_coefficients_3, circuit_coefficients_4, circuit_coefficients_5, circuit_coefficients_6, circuit_coefficients_7, circuit_coefficients_8, circuit_coefficients_9, circuit_coefficients_10, circuit_coefficients_11, circuit_coefficients_12, circuit_coefficients_13, circuit_coefficients_14, circuit_coefficients_15, circuit_coefficients_16, circuit_coefficients_17, circuit_coefficients_18, circuit_coefficients_19, circuit_coefficients_20, circuit_coefficients_21, circuit_coefficients_22, circuit_coefficients_23, circuit_coefficients_24, Bool.and_self]
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall t (List.mem_finRange t))
      e (List.mem_finRange e)) j (List.mem_finRange j))

theorem treeCoordinates_relation (t : Fin 125) (e : Fin 10) :
    integerTreeMatrix t *ᵥ treeCoordinates t e=integerGenerators e := by
  rw [treeCoordinates, Matrix.mulVec_mulVec,tree_mul_inverse,Matrix.one_mulVec]

theorem treeCoordinates_unique (t : Fin 125) (e : Fin 10) (c : Fin 4 → ℤ)
    (hc : integerTreeMatrix t *ᵥ c=integerGenerators e) : c=treeCoordinates t e := by
  have h := congrArg (fun v => treeInverse t *ᵥ v) hc
  dsimp only at h
  rw [Matrix.mulVec_mulVec,tree_inverse_mul,Matrix.one_mulVec] at h
  exact h

def fundamentalCircuitCoefficients (t : Fin 125) (e : Fin 10) : Fin 5 → ℤ :=
  Fin.cons 1 (-treeCoordinates t e)

def fundamentalCircuitColumns (t : Fin 125) (e : Fin 10) : Fin 5 → IntVec :=
  Fin.cons (integerGenerators e) (fun j => integerGenerators (treeEdges t j))

theorem fundamentalCircuit_coefficients (t : Fin 125) (e : Fin 10) (j : Fin 5) :
    fundamentalCircuitCoefficients t e j=0 ∨
      fundamentalCircuitCoefficients t e j=1 ∨
      fundamentalCircuitCoefficients t e j = -1 := by
  refine Fin.cases ?_ (fun j => ?_) j
  · exact Or.inr (Or.inl rfl)
  · change -treeCoordinates t e j=0 ∨ -treeCoordinates t e j=1 ∨ -treeCoordinates t e j = -1
    rcases treeCoordinates_zero_one_neg t e j with h|h|h <;> rw [h] <;> norm_num

theorem fundamentalCircuit_relation (t : Fin 125) (e : Fin 10) :
    ∑ j, fundamentalCircuitCoefficients t e j • fundamentalCircuitColumns t e j=0 := by
  ext i
  have h := congrFun (treeCoordinates_relation t e) i
  simp only [Matrix.mulVec, dotProduct,integerTreeMatrix] at h
  rw [Finset.sum_apply, Fin.sum_univ_succ]
  simp only [fundamentalCircuitCoefficients,fundamentalCircuitColumns,
    Fin.cons_zero,Fin.cons_succ,Finset.sum_apply,Pi.smul_apply,Pi.neg_apply,
    smul_eq_mul,one_mul,Pi.zero_apply,neg_mul,Finset.sum_neg_distrib]
  rw [show (∑ j, treeCoordinates t e j*integerGenerators (treeEdges t j) i)=
    integerGenerators e i by simpa only [mul_comm] using h]
  exact add_neg_cancel _

theorem liftingHeight_sum_preceding (n : ℕ) :
    (∑ j∈Finset.range n,(2:ℤ)^j)=2^n-1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring

theorem liftingHeight_largest_dominates (n : ℕ) :
    (∑ j∈Finset.range n,(2:ℤ)^j)<2^n := by
  rw [liftingHeight_sum_preceding]
  omega

end D4.Principal
