import D4.ConeAnalysisAssembly

/-! A strict facet comparison remains strict through the finite Jensen
and facet-count steps of the normalized-moment bound. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Finset ConePerspective

theorem normalized_bound_of_perspective_strict (n : ℕ) (hn : 2 ≤ n)
    (κ v j m u : ℝ) (hκ : 0 < κ) (hv : 0 < v) (hj : 0 < j) (hm : 0 < m)
    (hu : u ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2)))
    (h : momentPerspective n v j <
      m * profile n (profileConstant n κ) (((n:ℝ)-1)*κ) u) :
    m^(-2/(n:ℝ)) * coneNormalizedMoment n κ u <
      ConePerspective.normalizedMoment n v j := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hg := coneNormalizedMoment_pos n hn κ hκ hu
  have hg' : 0 < ConePerspective.normalizedMoment n v j := by
    unfold ConePerspective.normalizedMoment
    positivity
  rw [momentPerspective_eq_normalized n v j hn0 hv hj,
    profile_eq_coneNormalizedMoment n hn κ hκ hu] at h
  have he : (m^(-2/(n:ℝ))*coneNormalizedMoment n κ u)^(-(n:ℝ)/2) =
      m*coneNormalizedMoment n κ u^(-(n:ℝ)/2) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hm.le _) hg.le, ← Real.rpow_mul hm.le,
      show (-2/(n:ℝ))*(-(n:ℝ)/2) = 1 by field_simp, Real.rpow_one]
  rw [← he] at h
  exact (Real.rpow_lt_rpow_iff_of_neg hg' (mul_pos (Real.rpow_pos_of_pos hm _) hg)
    (by linarith)).mp h

theorem finite_perspective_bound_strict {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (n : ℕ) (hn : 2 ≤ n) (κ : ℝ) (hκ : 0 < κ) (v j ω : ι → ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hj : ∀ i ∈ s, 0 < j i)
    (hω : ∀ i ∈ s, ω i ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2)))
    (hp : ∀ i ∈ s, momentPerspective n (v i) (j i) <
      profile n (profileConstant n κ) (((n:ℝ)-1)*κ) (ω i)) :
    momentPerspective n (∑ i ∈ s, v i) (∑ i ∈ s, j i) <
      (s.card:ℝ)*profile n (profileConstant n κ) (((n:ℝ)-1)*κ)
        ((∑ i ∈ s, ω i)/(s.card:ℝ)) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hD : 0 < ((n:ℝ)-1)*κ := mul_pos (by linarith) hκ
  refine (momentPerspective_sum s hs n (by positivity) v j hv hj).trans_lt
    ((Finset.sum_lt_sum_of_nonempty hs hp).trans_le ?_)
  apply profile_sum_le_card s hs n hn _ _ (profileConstant_pos n κ hn' hκ) hD ω
  intro i hi
  rw [radiusAngle_image_positive n hn _ hD]
  exact hω i hi

theorem finite_normalized_bound_card_le_strict {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (n : ℕ) (hn : 2 ≤ n) (κ A f : ℝ) (hκ : 0 < κ) (v j ω : ι → ℝ)
    (hv : ∀ i ∈ s, 0 < v i) (hj : ∀ i ∈ s, 0 < j i)
    (hω : ∀ i ∈ s, ω i ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2)))
    (hsum : ∑ i ∈ s, ω i = A) (hcard : (s.card:ℝ) ≤ f)
    (hp : ∀ i ∈ s, momentPerspective n (v i) (j i) <
      profile n (profileConstant n κ) (((n:ℝ)-1)*κ) (ω i)) :
    f^(-2/(n:ℝ)) * coneNormalizedMoment n κ (A/f) <
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
  have H := finite_perspective_bound_strict s hs n hn κ hκ v j ω
    (fun i hi => (hv i hi).le) hj hω hp
  rw [hsum] at H
  have H' := count_profile_mono n hn (profileConstant n κ) (((n:ℝ)-1)*κ)
    A s.card f (profileConstant_pos n κ hn' hκ) (mul_pos (by linarith) hκ) hA hm hcard hmax
  have hfm : A/f ≤ A/(s.card:ℝ) :=
    (div_le_div_iff₀ hf hm).mpr (mul_le_mul_of_nonneg_left hcard hA.le)
  exact normalized_bound_of_perspective_strict n hn κ _ _ f (A/f) hκ
    (Finset.sum_pos hv hs) (Finset.sum_pos hj hs) hf
    ⟨div_pos hA hf, hfm.trans_lt hmax⟩ (H.trans_le H')


end D4.ConeAnalysis
