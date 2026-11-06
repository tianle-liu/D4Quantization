import D4.ParityQuantizer
import Mathlib.Algebra.Order.Round

noncomputable section
namespace D4.Quantizer
open Analytic
attribute [local instance] Classical.propDecidable
open scoped BigOperators

def rounded (x : Vec) : IntVec := fun i => round (x i)
def residual (x : Vec) : Vec := x - castVec (rounded x)
def correction (x : Vec) (i : Fin 4) : IntVec :=
  Pi.single i (if 0 ≤ residual x i then 1 else -1)

theorem residual_centeredCube (x : Vec) : residual x ∈ centeredCube := by
  change residual x ∈ Metric.closedBall 0 (1/2:ℝ)
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)).mpr
  intro i
  simpa only [residual,Pi.sub_apply,castVec,rounded,Real.norm_eq_abs] using abs_sub_round (x i)

theorem squaredError_rounding_translate (x : Vec) (z n : IntVec) :
    squaredError x (n+z) = squaredError (x-castVec n) z := by
  unfold squaredError
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.add_apply,Int.cast_add,Pi.sub_apply,castVec]
  ring

theorem correction_is_odd (x : Vec) (i : Fin 4) : correction x i ∉ evenSumLattice := by
  unfold correction
  split_ifs <;> simp [evenSumLattice]

theorem correction_error (x : Vec) (i : Fin 4) (hi : |residual x i| = ‖residual x‖) :
    squaredError (residual x) (correction x i) =
      squaredError (residual x) 0+1-2*‖residual x‖ := by
  unfold correction
  split_ifs with hp
  · rw [squaredError_single]
    rw [abs_of_nonneg hp] at hi
    norm_num
    linarith
  · rw [squaredError_single]
    rw [abs_of_neg (lt_of_not_ge hp)] at hi
    norm_num
    linarith

/-- Coordinate rounding already solves D4 nearest-point quantization when
its integer sum is even. This includes all rounding ties. -/
theorem rounded_even_optimal (x : Vec) (he : rounded x ∈ evenSumLattice) :
    rounded x ∈ evenSumLattice ∧
    ∀ z : IntVec, z ∈ evenSumLattice → squaredError x (rounded x) ≤ squaredError x z := by
  refine ⟨he,fun z hz => ?_⟩
  have h := squaredError_minimum (residual_centeredCube x) (z-rounded x)
  have hleft := squaredError_rounding_translate x 0 (rounded x)
  have hright := squaredError_rounding_translate x (z-rounded x) (rounded x)
  have heq : rounded x+(z-rounded x)=z := by abel
  simp only [add_zero,heq] at hleft hright
  simpa only [residual,← hleft,← hright] using h

/-- If rounding has odd sum, changing a coordinate of maximal absolute
residual toward its nearest alternative integer gives a closest D4 point. -/
theorem rounded_odd_optimal (x : Vec) (ho : rounded x ∉ evenSumLattice)
    (i : Fin 4) (hi : |residual x i| = ‖residual x‖) :
    rounded x + correction x i ∈ evenSumLattice ∧
    ∀ z : IntVec, z ∈ evenSumLattice →
      squaredError x (rounded x+correction x i) ≤ squaredError x z := by
  have hc := correction_is_odd x i
  constructor
  · change (2:ℤ) ∣ ∑ j, (rounded x+correction x i) j
    simp only [Pi.add_apply,Finset.sum_add_distrib]
    change ¬(2:ℤ) ∣ ∑ j, rounded x j at ho
    change ¬(2:ℤ) ∣ ∑ j, correction x i j at hc
    omega
  · intro z hz
    have hzo : z-rounded x ≠ 0 := by
      intro he
      have he' : z=rounded x := sub_eq_zero.mp he
      exact ho (he' ▸ hz)
    have h := squaredError_nonzero_gap (residual_centeredCube x) hzo
    rw [← correction_error x i hi] at h
    rw [squaredError_rounding_translate]
    have hz' := squaredError_rounding_translate x (z-rounded x) (rounded x)
    have heq : rounded x+(z-rounded x)=z := by abel
    rw [heq] at hz'
    rw [hz']
    exact h

/-- A maximal residual coordinate always exists, so the explicit correction
rule applies to every input. -/
theorem rounding_algorithm_total (x : Vec) :
    ∃ i : Fin 4, |residual x i| = ‖residual x‖ ∧
      let z := if rounded x ∈ evenSumLattice then rounded x else rounded x+correction x i
      z ∈ evenSumLattice ∧ ∀ w : IntVec, w ∈ evenSumLattice → squaredError x z ≤ squaredError x w := by
  obtain ⟨i,hi⟩ := exists_max_residual (residual x)
  refine ⟨i,hi,?_⟩
  dsimp only
  split_ifs with he
  · exact rounded_even_optimal x he
  · exact rounded_odd_optimal x he i hi

end D4.Quantizer
