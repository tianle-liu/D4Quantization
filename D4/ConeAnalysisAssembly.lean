import D4.ConeAnalysisBound

/-! Final finite real-number assembly of the facet estimate. Positivity,
Jensen, the exact normalization, and the facet-count comparison are all
proved here; identification of the summands is supplied by the geometric
decomposition theorems. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Finset ConePerspective

theorem finite_normalized_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (n : ℕ) (hn : 2 ≤ n) (κ A : ℝ) (hκ : 0 < κ) (v j ω : ι → ℝ)
    (hv : ∀ i ∈ s, 0 < v i) (hj : ∀ i ∈ s, 0 < j i)
    (hω : ∀ i ∈ s, ω i ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2)))
    (hsum : ∑ i ∈ s, ω i = A)
    (hp : ∀ i ∈ s, momentPerspective n (v i) (j i) ≤
      profile n (profileConstant n κ) (((n:ℝ)-1)*κ) (ω i)) :
    (s.card:ℝ)^(-2/(n:ℝ)) * coneNormalizedMoment n κ (A/(s.card:ℝ)) ≤
      ConePerspective.normalizedMoment n (∑ i ∈ s, v i) (∑ i ∈ s, j i) := by
  have hm : (0:ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  have hA : 0 < A := hsum ▸ Finset.sum_pos (fun i hi => (hω i hi).1) hs
  have hmax : A/(s.card:ℝ) < angle n (((n:ℝ)-1)*κ) (Real.pi/2) := by
    apply (div_lt_iff₀ hm).mpr
    rw [← hsum]
    simpa only [sum_const, nsmul_eq_mul, mul_comm] using
      Finset.sum_lt_sum_of_nonempty hs (fun i hi => (hω i hi).2)
  have H := finite_perspective_bound s hs n hn κ hκ v j ω
    (fun i hi => (hv i hi).le) hj hω hp
  rw [hsum] at H
  exact normalized_bound_of_perspective n hn κ _ _ _ _ hκ
    (Finset.sum_pos hv hs) (Finset.sum_pos hj hs) hm ⟨div_pos hA hm, hmax⟩ H

theorem finite_normalized_bound_card_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (n : ℕ) (hn : 2 ≤ n) (κ A f : ℝ) (hκ : 0 < κ) (v j ω : ι → ℝ)
    (hv : ∀ i ∈ s, 0 < v i) (hj : ∀ i ∈ s, 0 < j i)
    (hω : ∀ i ∈ s, ω i ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2)))
    (hsum : ∑ i ∈ s, ω i = A) (hcard : (s.card:ℝ) ≤ f)
    (hp : ∀ i ∈ s, momentPerspective n (v i) (j i) ≤
      profile n (profileConstant n κ) (((n:ℝ)-1)*κ) (ω i)) :
    f^(-2/(n:ℝ)) * coneNormalizedMoment n κ (A/f) ≤
      ConePerspective.normalizedMoment n (∑ i ∈ s, v i) (∑ i ∈ s, j i) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hm : (0:ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  have hf : 0 < f := hm.trans_le hcard
  have hA : 0 < A := hsum ▸ Finset.sum_pos (fun i hi => (hω i hi).1) hs
  have hmax : A/(s.card:ℝ) < angle n (((n:ℝ)-1)*κ) (Real.pi/2) := by
    apply (div_lt_iff₀ hm).mpr
    rw [← hsum]
    simpa only [sum_const, nsmul_eq_mul, mul_comm] using
      Finset.sum_lt_sum_of_nonempty hs (fun i hi => (hω i hi).2)
  have H := finite_perspective_bound s hs n hn κ hκ v j ω
    (fun i hi => (hv i hi).le) hj hω hp
  rw [hsum] at H
  have H' := count_profile_mono n hn (profileConstant n κ) (((n:ℝ)-1)*κ)
    A s.card f (profileConstant_pos n κ hn' hκ) (mul_pos (by linarith) hκ) hA hm hcard hmax
  have hfm : A/f ≤ A/(s.card:ℝ) :=
    (div_le_div_iff₀ hf hm).mpr (mul_le_mul_of_nonneg_left hcard hA.le)
  exact normalized_bound_of_perspective n hn κ _ _ f (A/f) hκ
    (Finset.sum_pos hv hs) (Finset.sum_pos hj hs) hf
    ⟨div_pos hA hf, hfm.trans_lt hmax⟩ (H.trans H')

theorem finite_normalized_lattice_count_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (n : ℕ) (hn : 2 ≤ n) (κ A : ℝ) (hκ : 0 < κ) (v j ω : ι → ℝ)
    (hv : ∀ i ∈ s, 0 < v i) (hj : ∀ i ∈ s, 0 < j i)
    (hω : ∀ i ∈ s, ω i ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2)))
    (hsum : ∑ i ∈ s, ω i = A) (hcard : s.card ≤ 2*(2^n-1))
    (hp : ∀ i ∈ s, momentPerspective n (v i) (j i) ≤
      profile n (profileConstant n κ) (((n:ℝ)-1)*κ) (ω i)) :
    (2*(2^n-1):ℕ)^(-2/(n:ℝ)) * coneNormalizedMoment n κ (A/(2*(2^n-1):ℕ)) ≤
      ConePerspective.normalizedMoment n (∑ i ∈ s, v i) (∑ i ∈ s, j i) := by
  exact finite_normalized_bound_card_le s hs n hn κ A (2*(2^n-1):ℕ) hκ v j ω
    hv hj hω hsum (by exact_mod_cast hcard) hp

end D4.ConeAnalysis
