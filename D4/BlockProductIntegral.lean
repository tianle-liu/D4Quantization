import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.BigOperators.Pi

/-! Fubini formulas on actual Cartesian products of measurable blocks.
No moment or volume identity is assumed. -/
noncomputable section
namespace D4.Blocks
open MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι]
variable {E : ι → Type*} [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))]

theorem pi_indicator_product (s : ∀ i, Set (E i)) (f : ∀ i, E i → ℝ)
    (x : ∀ i, E i) :
    (univ.pi s).indicator (fun y => ∏ i, f i (y i)) x =
      ∏ i, (s i).indicator (f i) (x i) := by
  classical
  by_cases h : x ∈ univ.pi s
  · rw [indicator_of_mem h]
    exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (h i (mem_univ i)) _).symm
  · rw [indicator_of_not_mem h]
    have hn : ∃ i, x i ∉ s i := by simpa only [mem_pi, mem_univ, forall_true_left, not_forall] using h
    obtain ⟨i,hi⟩ := hn
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_not_mem hi _)).symm

theorem integral_pi_product (s : ∀ i, Set (E i)) (hs : ∀ i, MeasurableSet (s i))
    (f : ∀ i, E i → ℝ) :
    (∫ x in univ.pi s, ∏ i, f i (x i)) = ∏ i, ∫ y in s i, f i y := by
  rw [← integral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [pi_indicator_product]
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_congr rfl fun i _ => integral_indicator (hs i)

theorem integrableOn_pi_product (s : ∀ i, Set (E i)) (hs : ∀ i, MeasurableSet (s i))
    (f : ∀ i, E i → ℝ) (hf : ∀ i, IntegrableOn (f i) (s i)) :
    IntegrableOn (fun x => ∏ i, f i (x i)) (univ.pi s) := by
  apply (integrable_indicator_iff (MeasurableSet.univ_pi hs)).mp
  convert (Integrable.fintype_prod_dep (fun i => (integrable_indicator_iff (hs i)).mpr (hf i))) using 1
  funext x
  exact pi_indicator_product s f x

theorem volume_real_pi (s : ∀ i, Set (E i)) :
    volume.real (univ.pi s) = ∏ i, volume.real (s i) := by
  simp only [measureReal_def, volume_pi_pi, ENNReal.toReal_prod]

variable [DecidableEq ι]

theorem integral_pi_coordinate (s : ∀ i, Set (E i)) (hs : ∀ i, MeasurableSet (s i))
    (f : ∀ i, E i → ℝ) (i : ι) :
    (∫ x in univ.pi s, f i (x i)) =
      (∫ y in s i, f i y) * ∏ j ∈ Finset.univ.erase i, volume.real (s j) := by
  have h := integral_pi_product s hs (fun j y => if j=i then f j y else 1)
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true] at h
  rw [h, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hji, Measure.real, Measure.restrict_apply_univ]

theorem integrableOn_pi_coordinate (s : ∀ i, Set (E i)) (hs : ∀ i, MeasurableSet (s i))
    (hfinite : ∀ i, volume (s i) < ⊤) (f : ∀ i, E i → ℝ)
    (hf : ∀ i, IntegrableOn (f i) (s i)) (i : ι) :
    IntegrableOn (fun x => f i (x i)) (univ.pi s) := by
  have h := integrableOn_pi_product s hs (fun j y => if j=i then f j y else 1) (by
    intro j
    by_cases hji : j=i
    · simpa only [hji, if_true] using hf j
    · simpa only [hji, if_false] using
        ((integrableOn_const (C := (1:ℝ))).mpr (Or.inr (hfinite j))))
  simpa only [Finset.prod_ite_eq', Finset.mem_univ, if_true] using h

theorem integral_pi_sum (s : ∀ i, Set (E i)) (hs : ∀ i, MeasurableSet (s i))
    (hfinite : ∀ i, volume (s i) < ⊤) (f : ∀ i, E i → ℝ)
    (hf : ∀ i, IntegrableOn (f i) (s i)) :
    (∫ x in univ.pi s, ∑ i, f i (x i)) =
      ∑ i, (∫ y in s i, f i y) * ∏ j ∈ Finset.univ.erase i, volume.real (s j) := by
  rw [integral_finset_sum _ (fun i _ => integrableOn_pi_coordinate s hs hfinite f hf i)]
  exact Finset.sum_congr rfl fun i _ => integral_pi_coordinate s hs f i

end D4.Blocks
