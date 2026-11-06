import D4.ParityNearest
import D4.FundamentalDomain
import D4.EuclideanMoment
import D4.BasisChange

/-! A genuine fundamental domain of the even-sum lattice, of volume two. -/
noncomputable section
open Matrix MeasureTheory Set

namespace D4.Quantizer
open Analytic

def parityBox : Set Vec :=
  {x | (-1/2 : ℝ) ≤ x 0 ∧ x 0 < 3/2 ∧
    ∀ i : Fin 4, i ≠ 0 → (-1/2 : ℝ) ≤ x i ∧ x i < 1/2}

theorem parityBox_measurable : MeasurableSet parityBox := by
  unfold parityBox
  have hm (i : Fin 4) : Measurable (fun x : Vec => x i) := measurable_pi_apply i
  have hh : MeasurableSet {x : Vec | ∀ i : Fin 4, i ≠ 0 →
      (-1/2 : ℝ) ≤ x i ∧ x i < 1/2} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun i : Fin 4 => MeasurableSet.iInter fun _ : i ≠ 0 =>
      (measurableSet_le measurable_const (hm i)).inter
        (measurableSet_lt (hm i) measurable_const)
  exact (measurableSet_le measurable_const (hm 0)).inter
    ((measurableSet_lt (hm 0) measurable_const).inter hh)

theorem even_translate_into_parityBox (x : Vec) :
    ∃ z : IntVec, z ∈ evenSumLattice ∧ castVec z + x ∈ parityBox := by
  let k : IntVec := fun i => ⌊x i + 1/2⌋
  let s : ℤ := ∑ i, k i
  let r : ℤ := s % 2
  let z : IntVec := fun i => -k i + if i = 0 then r else 0
  have hr0 : 0 ≤ r := Int.emod_nonneg s (by norm_num)
  have hr1 : r ≤ 1 := by have := Int.emod_lt_of_pos s (by norm_num : (0 : ℤ) < 2); omega
  have hzsum : ∑ i, z i = -s + r := by
    simp [z, s, Finset.sum_add_distrib]
  refine ⟨z, ?_, ?_⟩
  · change (2 : ℤ) ∣ ∑ i, z i
    rw [hzsum]
    exact Int.dvd_of_emod_eq_zero (by dsimp [r]; omega)
  · have hc (i : Fin 4) : (-1/2 : ℝ) ≤ -(k i : ℝ) + x i ∧
        -(k i : ℝ) + x i < 1/2 := by
      have h1 := Int.floor_le (x i + 1/2)
      have h2 := Int.lt_floor_add_one (x i + 1/2)
      dsimp [k]
      constructor <;> linarith
    have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
    have hr1' : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
    change (-1/2 : ℝ) ≤ (z 0 : ℝ) + x 0 ∧ (z 0 : ℝ) + x 0 < 3/2 ∧ _
    dsimp only [z]
    simp only [ite_true, Int.cast_add, Int.cast_neg]
    refine ⟨by linarith [(hc 0).1], by linarith [(hc 0).2], ?_⟩
    intro i hi
    change (-1/2 : ℝ) ≤ (z i : ℝ) + x i ∧ (z i : ℝ) + x i < 1/2
    simpa [z, hi] using hc i

theorem even_translate_parityBox_unique (x : Vec) {z w : IntVec}
    (hz : z ∈ evenSumLattice) (hw : w ∈ evenSumLattice)
    (hzx : castVec z + x ∈ parityBox) (hwx : castVec w + x ∈ parityBox) : z = w := by
  have hcoord (i : Fin 4) (hi : i ≠ 0) : z i = w i := by
    have hz' := hzx.2.2 i hi
    have hw' := hwx.2.2 i hi
    change (-1/2 : ℝ) ≤ (z i : ℝ) + x i ∧ (z i : ℝ) + x i < 1/2 at hz'
    change (-1/2 : ℝ) ≤ (w i : ℝ) + x i ∧ (w i : ℝ) + x i < 1/2 at hw'
    have hu : (z i : ℝ) - (w i : ℝ) < 1 := by linarith
    have hl : (-1 : ℝ) < (z i : ℝ) - (w i : ℝ) := by linarith
    have hu' : z i - w i < 1 := by exact_mod_cast hu
    have hl' : -1 < z i - w i := by exact_mod_cast hl
    omega
  have hdiv : (2 : ℤ) ∣ z 0 - w 0 := by
    have h := dvd_sub hz hw
    change (2 : ℤ) ∣ (∑ i, z i) - ∑ i, w i at h
    simpa [Fin.sum_univ_four, hcoord 1 (by decide), hcoord 2 (by decide),
      hcoord 3 (by decide)] using h
  have hz' : (-1/2 : ℝ) ≤ (z 0 : ℝ) + x 0 ∧ (z 0 : ℝ) + x 0 < 3/2 :=
    ⟨hzx.1, hzx.2.1⟩
  have hw' : (-1/2 : ℝ) ≤ (w 0 : ℝ) + x 0 ∧ (w 0 : ℝ) + x 0 < 3/2 :=
    ⟨hwx.1, hwx.2.1⟩
  have hu : (z 0 : ℝ) - (w 0 : ℝ) < 2 := by linarith
  have hl : (-2 : ℝ) < (z 0 : ℝ) - (w 0 : ℝ) := by linarith
  have hu' : z 0 - w 0 < 2 := by exact_mod_cast hu
  have hl' : -2 < z 0 - w 0 := by exact_mod_cast hl
  have hzero : z 0 = w 0 := by omega
  ext i
  by_cases hi : i = 0
  · simpa [hi] using hzero
  · exact hcoord i hi

attribute [local instance] integerTranslation

def parityCoordinateDomain : Set Vec := basisEquiv ⁻¹' parityBox

theorem parityCoordinateDomain_fundamental :
    IsAddFundamentalDomain IntVec parityCoordinateDomain volume := by
  have hm : Measurable basisEquiv := basisEquiv.toContinuousLinearEquiv.continuous.measurable
  apply IsAddFundamentalDomain.mk' (hm parityBox_measurable).nullMeasurableSet
  intro x
  obtain ⟨z, hz, hzx⟩ := even_translate_into_parityBox (basisEquiv x)
  obtain ⟨n, hn⟩ := evenSumLattice_has_preimage z hz
  have hc (m : IntVec) : basisEquiv (m +ᵥ x) = castVec (basisMatrixZ *ᵥ m) + basisEquiv x := by
    rw [integer_vadd, map_add, basisEquiv_apply, ← cast_basis_mulVec]
  refine ⟨n, ?_, ?_⟩
  · change basisEquiv (n +ᵥ x) ∈ parityBox
    rwa [hc, hn]
  · intro m hm
    change basisEquiv (m +ᵥ x) ∈ parityBox at hm
    rw [hc] at hm
    have he := even_translate_parityBox_unique (basisEquiv x)
      (basisMatrixZ_mulVec_mem m) hz hm hzx
    rw [← hn] at he
    apply castVec_injective
    apply basisEquiv.injective
    simpa only [basisEquiv_apply, ← cast_basis_mulVec] using congrArg castVec he

end D4.Quantizer
