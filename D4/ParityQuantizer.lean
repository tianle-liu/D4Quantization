import D4.Lattice
import D4.CubicIntegral

/-!
# Coordinate rounding and the parity correction

All comparisons below are with every integer vector, including ties on the
rounding-cell boundary. The correction changes a coordinate whose absolute
rounding residual is maximal.
-/
noncomputable section
open Matrix Finset

namespace D4.Quantizer
open Analytic

def squaredError (x : Vec) (z : IntVec) : ℝ :=
  ∑ i, (x i - (z i : ℝ))^2

theorem scalar_integer_gap {r : ℝ} (hr : |r| ≤ 1/2) {k : ℤ} (hk : k ≠ 0) :
    1-2*|r| ≤ (r-(k : ℝ))^2-r^2 := by
  have ha : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hm : r*(k : ℝ) ≤ |r| * |(k : ℝ)| := by
    simpa only [abs_mul] using le_abs_self (r*(k : ℝ))
  have hp : 0 ≤ (|(k : ℝ)|-1) * (|(k : ℝ)|+1-2*|r|) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith only [ha, hm, hp, sq_abs (k : ℝ)]

theorem scalar_integer_minimum {r : ℝ} (hr : |r| ≤ 1/2) (k : ℤ) :
    0 ≤ (r-(k : ℝ))^2-r^2 := by
  by_cases hk : k = 0
  · simp [hk]
  · have h := scalar_integer_gap hr hk
    linarith

theorem coordinate_bound {x : Vec} (hx : x ∈ centeredCube) (i : Fin 4) : |x i| ≤ 1/2 := by
  have hn : ‖x‖ ≤ 1/2 := by simpa [centeredCube, Metric.mem_closedBall] using hx
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  exact hi.trans hn

theorem squaredError_minimum {x : Vec} (hx : x ∈ centeredCube) (z : IntVec) :
    squaredError x 0 ≤ squaredError x z := by
  apply Finset.sum_le_sum
  intro i hi
  simpa only [Pi.zero_apply, Int.cast_zero, sub_zero] using
    (sub_nonneg.mp (scalar_integer_minimum (coordinate_bound hx i) (z i)))

theorem squaredError_nonzero_gap {x : Vec} (hx : x ∈ centeredCube)
    {z : IntVec} (hz : z ≠ 0) :
    squaredError x 0 + 1 - 2*‖x‖ ≤ squaredError x z := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hz
    ext i
    exact h i
  have hs := Finset.single_le_sum
    (s := Finset.univ) (f := fun j => (x j - (z j : ℝ))^2-(x j)^2)
    (fun j _ => scalar_integer_minimum (coordinate_bound hx j) (z j)) (Finset.mem_univ i)
  have hg := scalar_integer_gap (coordinate_bound hx i) hi
  have hn : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have he : ∑ j : Fin 4, ((x j - (z j : ℝ))^2-(x j)^2) =
      squaredError x z - squaredError x 0 := by
    simp [squaredError, Finset.sum_sub_distrib]
  rw [he] at hs
  dsimp only at hs
  linarith only [hs, hg, hn]

theorem exists_max_residual (x : Vec) : ∃ i : Fin 4, |x i| = ‖x‖ := by
  obtain ⟨i, hi, hm⟩ := Finset.exists_max_image Finset.univ (fun i : Fin 4 => |x i|)
    (by simp)
  refine ⟨i, le_antisymm ?_ ?_⟩
  · simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
    intro j
    simpa only [Real.norm_eq_abs] using hm j (Finset.mem_univ j)

theorem squaredError_single (x : Vec) (i : Fin 4) (k : ℤ) :
    squaredError x (Pi.single i k) = squaredError x 0 + (k : ℝ)^2 - 2*x i*k := by
  classical
  have he : squaredError x (Pi.single i k) =
      (∑ j, (x j)^2) + ∑ j : Fin 4, if j=i then (k : ℝ)^2-2*x j*k else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : j=i <;> simp [Pi.single_apply, h, eq_comm] <;> ring
  rw [he]
  simp [squaredError, Finset.sum_ite_eq']
  ring

/-- The optimal parity correction, including ties in the maximal residual. -/
theorem exists_odd_correction {x : Vec} (hx : x ∈ centeredCube) :
    ∃ z : IntVec, z ∉ evenSumLattice ∧
      squaredError x z = squaredError x 0 + 1 - 2*‖x‖ ∧
      ∀ w : IntVec, w ∉ evenSumLattice → squaredError x z ≤ squaredError x w := by
  obtain ⟨i, hi⟩ := exists_max_residual x
  have build (k : ℤ) (hodd : ¬ (2 : ℤ) ∣ k)
      (hval : (k : ℝ)^2-2*x i*k = 1-2*‖x‖) :
      ∃ z : IntVec, z ∉ evenSumLattice ∧
        squaredError x z = squaredError x 0 + 1 - 2*‖x‖ ∧
        ∀ w : IntVec, w ∉ evenSumLattice → squaredError x z ≤ squaredError x w := by
    classical
    refine ⟨Pi.single i k, ?_, ?_, ?_⟩
    · simpa [evenSumLattice] using hodd
    · rw [squaredError_single]
      linarith only [hval]
    · intro w hw
      have hw0 : w ≠ 0 := by
        intro he
        apply hw
        simp [he, evenSumLattice]
      rw [squaredError_single]
      have hh := squaredError_nonzero_gap hx hw0
      linarith only [hval, hh]
  by_cases hp : 0 ≤ x i
  · apply build 1 (by norm_num)
    rw [abs_of_nonneg hp] at hi
    norm_num
    linarith
  · apply build (-1) (by norm_num)
    rw [abs_of_neg (lt_of_not_ge hp)] at hi
    norm_num
    linarith

end D4.Quantizer
