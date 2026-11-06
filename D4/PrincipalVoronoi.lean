import D4.PrincipalSupport

/-!
# The principal zonotope is the true dual Voronoi cell

Sorting the five vertex potentials decomposes every real test vector into
four nonnegative multiples of integer cut vectors. Their edge differences
are zero or units, so their squared differences equal absolute differences.
-/
noncomputable section
open Matrix Set
namespace D4.Principal
open Analytic

def level (k : Fin 4) (i : Fin 5) : ℝ := if k.val < i.val then 1 else 0

theorem level_difference (a : Fin 5 → ℝ) (i j : Fin 5) :
    a i - a j = ∑ k : Fin 4, (a k.succ - a k.castSucc) * (level k i - level k j) := by
  have hs (t : Fin 5) :
      a t - a 0 = ∑ k : Fin 4, (a k.succ - a k.castSucc) * level k t := by
    fin_cases t
    · rw [Fin.sum_univ_four]
      change a 0 - a 0 = (a 1 - a 0) * 0 + (a 2 - a 1) * 0 + (a 3 - a 2) * 0 + (a 4 - a 3) * 0
      ring
    · rw [Fin.sum_univ_four]
      change a 1 - a 0 = (a 1 - a 0) * 1 + (a 2 - a 1) * 0 + (a 3 - a 2) * 0 + (a 4 - a 3) * 0
      ring
    · rw [Fin.sum_univ_four]
      change a 2 - a 0 = (a 1 - a 0) * 1 + (a 2 - a 1) * 1 + (a 3 - a 2) * 0 + (a 4 - a 3) * 0
      ring
    · rw [Fin.sum_univ_four]
      change a 3 - a 0 = (a 1 - a 0) * 1 + (a 2 - a 1) * 1 + (a 3 - a 2) * 1 + (a 4 - a 3) * 0
      ring
    · rw [Fin.sum_univ_four]
      change a 4 - a 0 = (a 1 - a 0) * 1 + (a 2 - a 1) * 1 + (a 3 - a 2) * 1 + (a 4 - a 3) * 1
      ring
  calc
    a i - a j = (a i - a 0) - (a j - a 0) := by ring
    _ = (∑ k : Fin 4, (a k.succ - a k.castSucc) * level k i) -
        ∑ k : Fin 4, (a k.succ - a k.castSucc) * level k j := by rw [hs i, hs j]
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem level_mono (k : Fin 4) : Monotone (level k) := by
  intro i j hij
  by_cases hi : k.val < i.val
  · have hj : k.val < j.val := lt_of_lt_of_le hi hij
    simp only [level, hi, hj, ite_true, le_refl]
  · simp only [level, hi, ite_false]
    split_ifs <;> norm_num

theorem level_abs_difference (a : Fin 5 → ℝ) (ha : Monotone a) (i j : Fin 5) :
    |a i - a j| = ∑ k : Fin 4, (a k.succ - a k.castSucc) * |level k i - level k j| := by
  rcases le_total i j with hij | hji
  · rw [abs_of_nonpos (sub_nonpos.mpr (ha hij))]
    simp_rw [abs_of_nonpos (sub_nonpos.mpr (level_mono _ hij))]
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib, ← level_difference]
  · rw [abs_of_nonneg (sub_nonneg.mpr (ha hji))]
    simp_rw [abs_of_nonneg (sub_nonneg.mpr (level_mono _ hji))]
    exact level_difference a i j

def potential (x : Vec) : Fin 5 → ℝ := Fin.cons 0 x

def edgePos : Fin 10 → Fin 5 := ![1,2,3,4,1,1,1,2,2,3]
def edgeNeg : Fin 10 → Fin 5 := ![0,0,0,0,2,3,4,3,4,4]

theorem generator_dot_potential (x : Vec) (e : Fin 10) :
    dotProduct x (cone1Vectors e) = potential x (edgePos e) - potential x (edgeNeg e) := by
  fin_cases e
  · rw [dotProduct, Fin.sum_univ_four]
    change x 0 * (1) + x 1 * (0) + x 2 * (0) + x 3 * (0) = x 0 - 0
    ring
  · rw [dotProduct, Fin.sum_univ_four]
    change x 0 * (0) + x 1 * (1) + x 2 * (0) + x 3 * (0) = x 1 - 0
    ring
  · rw [dotProduct, Fin.sum_univ_four]
    change x 0 * (0) + x 1 * (0) + x 2 * (1) + x 3 * (0) = x 2 - 0
    ring
  · rw [dotProduct, Fin.sum_univ_four]
    change x 0 * (0) + x 1 * (0) + x 2 * (0) + x 3 * (1) = x 3 - 0
    ring
  · rw [dotProduct, Fin.sum_univ_four]
    change x 0 * (1) + x 1 * (-1) + x 2 * (0) + x 3 * (0) = x 0 - x 1
    ring
  · rw [dotProduct, Fin.sum_univ_four]
    change x 0 * (1) + x 1 * (0) + x 2 * (-1) + x 3 * (0) = x 0 - x 2
    ring
  · rw [dotProduct, Fin.sum_univ_four]
    change x 0 * (1) + x 1 * (0) + x 2 * (0) + x 3 * (-1) = x 0 - x 3
    ring
  · rw [dotProduct, Fin.sum_univ_four]
    change x 0 * (0) + x 1 * (1) + x 2 * (-1) + x 3 * (0) = x 1 - x 2
    ring
  · rw [dotProduct, Fin.sum_univ_four]
    change x 0 * (0) + x 1 * (1) + x 2 * (0) + x 3 * (-1) = x 1 - x 3
    ring
  · rw [dotProduct, Fin.sum_univ_four]
    change x 0 * (0) + x 1 * (0) + x 2 * (1) + x 3 * (-1) = x 2 - x 3
    ring

def sortedPotential (x : Vec) : Fin 5 → ℝ := potential x ∘ Tuple.sort (potential x)
def gap (x : Vec) (k : Fin 4) : ℝ := sortedPotential x k.succ - sortedPotential x k.castSucc

def cut (x : Vec) (k : Fin 4) : IntVec := fun i =>
  (if k.val < ((Tuple.sort (potential x)).symm i.succ).val then 1 else 0) -
  (if k.val < ((Tuple.sort (potential x)).symm 0).val then 1 else 0)

theorem gap_nonneg (x : Vec) (k : Fin 4) : 0 ≤ gap x k := by
  apply sub_nonneg.mpr
  exact Tuple.monotone_sort (potential x) (show k.castSucc ≤ k.succ by simp [Fin.le_def])

theorem cut_cast (x : Vec) (k : Fin 4) (i : Fin 4) :
    castVec (cut x k) i =
      level k ((Tuple.sort (potential x)).symm i.succ) -
      level k ((Tuple.sort (potential x)).symm 0) := by
  simp only [castVec, cut, level, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero]

theorem potential_cut (x : Vec) (k : Fin 4) (i : Fin 5) :
    potential (castVec (cut x k)) i =
      level k ((Tuple.sort (potential x)).symm i) -
      level k ((Tuple.sort (potential x)).symm 0) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [potential]
  · exact cut_cast x k j

theorem sortedPotential_unsort (x : Vec) (i : Fin 5) :
    sortedPotential x ((Tuple.sort (potential x)).symm i) = potential x i := by
  simp [sortedPotential]

theorem vector_cut_decomposition (x : Vec) :
    x = ∑ k : Fin 4, gap x k • castVec (cut x k) := by
  ext i
  have h := level_difference (sortedPotential x)
    ((Tuple.sort (potential x)).symm i.succ) ((Tuple.sort (potential x)).symm 0)
  rw [sortedPotential_unsort, sortedPotential_unsort] at h
  change x i - 0 = ∑ k : Fin 4, gap x k *
    (level k ((Tuple.sort (potential x)).symm i.succ) -
     level k ((Tuple.sort (potential x)).symm 0)) at h
  rw [sub_zero] at h
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cut_cast]
  exact h

theorem cut_generator_dot (x : Vec) (k : Fin 4) (e : Fin 10) :
    dotProduct (castVec (cut x k)) (cone1Vectors e) =
      level k ((Tuple.sort (potential x)).symm (edgePos e)) -
      level k ((Tuple.sort (potential x)).symm (edgeNeg e)) := by
  rw [generator_dot_potential, potential_cut, potential_cut]
  ring

theorem cut_abs_eq_sq (x : Vec) (k : Fin 4) (e : Fin 10) :
    |dotProduct (castVec (cut x k)) (cone1Vectors e)| =
      (dotProduct (castVec (cut x k)) (cone1Vectors e))^2 := by
  rw [cut_generator_dot]
  unfold level
  split_ifs <;> norm_num

theorem generator_abs_cut_decomposition (x : Vec) (e : Fin 10) :
    |dotProduct x (cone1Vectors e)| =
      ∑ k : Fin 4, gap x k * |dotProduct (castVec (cut x k)) (cone1Vectors e)| := by
  have h := level_abs_difference (sortedPotential x) (Tuple.monotone_sort (potential x))
    ((Tuple.sort (potential x)).symm (edgePos e))
    ((Tuple.sort (potential x)).symm (edgeNeg e))
  rw [sortedPotential_unsort, sortedPotential_unsort] at h
  rw [generator_dot_potential]
  simp_rw [cut_generator_dot]
  exact h

theorem support_cut_decomposition (w : Fin 10 → ℝ) (x : Vec) :
    support w x = ∑ k : Fin 4, gap x k * quadratic (principalForm w) (castVec (cut x k)) := by
  have hh : support w x = ∑ e, w e *
      ∑ k : Fin 4, gap x k * |dotProduct (castVec (cut x k)) (cone1Vectors e)| := by
    unfold support
    apply Finset.sum_congr rfl
    intro e _
    rw [generator_abs_cut_decomposition]
  rw [hh]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [quadratic_principal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [cut_abs_eq_sq]
  ring

theorem dot_cut_decomposition (x r : Vec) :
    dotProduct x r = ∑ k : Fin 4, gap x k * dotProduct (castVec (cut x k)) r := by
  calc
    dotProduct x r = dotProduct (∑ k : Fin 4, gap x k • castVec (cut x k)) r :=
      congrArg (fun y => dotProduct y r) (vector_cut_decomposition x)
    _ = _ := by
      simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Integer inequalities already imply every real support inequality. -/
theorem integer_support_implies_real_support (w : Fin 10 → ℝ) (r : Vec)
    (hr : ∀ z : IntVec, dotProduct (castVec z) r ≤ quadratic (principalForm w) (castVec z))
    (x : Vec) : dotProduct x r ≤ support w x := by
  rw [dot_cut_decomposition, support_cut_decomposition]
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left (hr (cut x k)) (gap_nonneg x k)

/-- The converse geometric inclusion uses only the genuine integer Voronoi
inequalities. In particular, completeness of a finite list of sites is not assumed. -/
theorem voronoi_subset_zonotope_preimage {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e) :
    voronoi (principalForm w) ⊆
      (fun x : Vec => (2 : ℝ) • (principalForm w *ᵥ x)) ⁻¹' zonotope w := by
  intro x hx
  apply (mem_zonotope_iff_support hw _).mpr
  apply integer_support_implies_real_support
  intro z
  have h := hx z
  rw [quadratic_sub_vec (principal_isHermitian w)] at h
  simp only [dotProduct_smul, smul_eq_mul]
  rw [quadratic_pair_symmetric (principal_isHermitian w) (castVec z) x]
  linarith

/-- Exact equality of the dual zonotope and the Voronoi cell, including
nonnegative boundary weights. -/
theorem voronoi_eq_zonotope_preimage {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e) :
    voronoi (principalForm w) =
      (fun x : Vec => (2 : ℝ) • (principalForm w *ᵥ x)) ⁻¹' zonotope w :=
  Set.Subset.antisymm (voronoi_subset_zonotope_preimage hw)
    (zonotope_preimage_subset_voronoi hw)

end D4.Principal
