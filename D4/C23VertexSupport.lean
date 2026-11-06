import D4.C23VertexData

/-! Every proposed vertex satisfies the inequalities for every integer site.
No Delaunay classification or finite-site assumption is used here. -/
noncomputable section
namespace D4.Secondary
open Matrix Analytic Quantizer

theorem realMatrix_basisTranspose :
    realMatrix basisMatrixZ.transpose = (basisMatrix ℝ).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [realMatrix, basisMatrix]

theorem d4_vertex_support (t : Fin 24) :
    DualSupport (gramMatrix ℝ) (castVec (d4DualVertex t)) := by
  classical
  let p : Vec := (1/2 : ℝ) • castVec (d4PhysicalTwice t)
  have hmin : ∀ z : IntVec, z ∈ evenSumLattice → squaredError p 0 ≤ squaredError p z := by
    rcases d4_physical_cases t with hh | ⟨i, hi | hi⟩
    · intro z _
      apply physical_half_minimum p
      intro j
      have hb : |(d4PhysicalTwice t j : ℝ)| ≤ 1 := by exact_mod_cast hh j
      change |(1/2 : ℝ) * (d4PhysicalTwice t j : ℝ)| ≤ 1/2
      rw [abs_mul]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
      nlinarith
    · have hp : p = castVec (Pi.single i (1 : ℤ)) := by
        ext j
        by_cases hj : j = i <;> simp [p, hi, castVec, Pi.single_apply, hj]
      rw [hp]
      exact physical_odd_minimum _ (by simp [evenSumLattice])
        (by simp [squaredError, castVec, Pi.single_apply])
    · have hp : p = castVec (Pi.single i (-1 : ℤ)) := by
        ext j
        by_cases hj : j = i <;> simp [p, hi, castVec, Pi.single_apply, hj]
      rw [hp]
      exact physical_odd_minimum _ (by simp [evenSumLattice])
        (by simp [squaredError, castVec, Pi.single_apply])
  have h := gram_support_of_minimum p hmin
  have he : (2 : ℝ) • ((basisMatrix ℝ).transpose *ᵥ p) = castVec (d4DualVertex t) := by
    calc
      _ = (basisMatrix ℝ).transpose *ᵥ castVec (d4PhysicalTwice t) := by
        simp [p, Matrix.mulVec_smul, smul_smul]
      _ = castVec (basisMatrixZ.transpose *ᵥ d4PhysicalTwice t) := by
        rw [castVec_mulVec, realMatrix_basisTranspose]
      _ = _ := by rw [d4_dual_basis]
  rwa [he] at h

theorem dualSupport_linear_combination {ι : Type*} [Fintype ι]
    (Q : ι → Gram) (r : ι → Vec) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hr : ∀ i, DualSupport (Q i) (r i)) :
    DualSupport (∑ i, w i • Q i) (∑ i, w i • r i) := by
  intro z
  rw [Principal.quadratic_sum]
  have hd : dotProduct (castVec z) (∑ i, w i • r i) =
      ∑ i, w i * dotProduct (castVec z) (r i) := by
    simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hd]
  simp only [quadratic_smul]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hr i z) (hw i))

def secondaryVertex (v : Fin 120 → Fin 10 → IntVec) (w : Fin 10 → ℝ)
    (t : Fin 120) : Vec := ∑ k, w k • castVec (v t k)

def secondaryGenerator (g : Fin 9 → Vec) : Fin 10 → Gram :=
  Fin.cases (gramMatrix ℝ) (fun j => rankOne (g j))

theorem secondaryGenerator_sum (g : Fin 9 → Vec) (w : Fin 10 → ℝ) :
    (∑ k, w k • secondaryGenerator g k) =
      secondaryForm g (w 0) (fun j => w j.succ) := by
  rw [Fin.sum_univ_succ]
  rfl

theorem secondaryVertex_support
    (v : Fin 120 → Fin 10 → IntVec) (g : Fin 9 → IntVec)
    (aIndex : Fin 120 → Fin 24)
    (hA : ∀ t, v t 0 = d4DualVertex (aIndex t))
    (hR : ∀ t j, v t j.succ = g j ∨ v t j.succ = -g j)
    (w : Fin 10 → ℝ) (hw : ∀ k, 0 ≤ w k) (t : Fin 120) :
    DualSupport (secondaryForm (fun j => castVec (g j)) (w 0) (fun j => w j.succ))
      (secondaryVertex v w t) := by
  rw [← secondaryGenerator_sum]
  apply dualSupport_linear_combination _ _ w hw
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · change DualSupport (gramMatrix ℝ) (castVec (v t 0))
    rw [hA]
    exact d4_vertex_support _
  · change DualSupport (rankOne (castVec (g j))) (castVec (v t j.succ))
    rcases hR t j with hr | hr
    · rw [hr]
      simpa using rankOne_support (g j) 1 (Or.inl rfl)
    · rw [hr]
      have he : castVec (-g j) = (-1 : ℝ) • castVec (g j) := by
        ext i
        simp [castVec]
      rw [he]
      simpa only [Int.cast_neg, Int.cast_one] using rankOne_support (g j) (-1) (Or.inr rfl)

theorem c2_vertex_support (w : Fin 10 → ℝ) (hw : ∀ k, 0 ≤ w k) (t : Fin 120) :
    DualSupport (secondaryForm cone2Vectors (w 0) (fun j => w j.succ))
      (secondaryVertex c2VertexCoefficients w t) := by
  simpa only [c2_generators_cast] using secondaryVertex_support c2VertexCoefficients
    c2IntegerGenerators c2VertexAIndex c2_vertex_A c2_vertex_rankOne w hw t

theorem c3_vertex_support (w : Fin 10 → ℝ) (hw : ∀ k, 0 ≤ w k) (t : Fin 120) :
    DualSupport (secondaryForm cone3Vectors (w 0) (fun j => w j.succ))
      (secondaryVertex c3VertexCoefficients w t) := by
  simpa only [c3_generators_cast] using secondaryVertex_support c3VertexCoefficients
    c3IntegerGenerators c3VertexAIndex c3_vertex_A c3_vertex_rankOne w hw t

end D4.Secondary
