import D4.ConePerspectiveRadial

/-! Assembly of the analytic facet bound. The angle-dependent normalized
cone moment is defined from the explicit circular-cone formulas and the
proved inverse of the angle integral. Geometric facet decomposition and
polar integration are not assumptions of any cone-integration theorem here. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Finset ConePerspective

def coneNormalizedMoment (n : ℕ) (κ u : ℝ) : ℝ :=
  let r := inverseRadius n (((n:ℝ)-1)*κ) u
  ConePerspective.normalizedMoment n (coneVolume n κ r) (coneMoment n κ r)

theorem coneNormalizedMoment_pos (n : ℕ) (hn : 2 ≤ n) (κ : ℝ) (hκ : 0 < κ)
    {u : ℝ} (hu : u ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2))) :
    0 < coneNormalizedMoment n κ u := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hr := (inverseRadius_spec n hn _ (mul_pos (by linarith) hκ) hu).1
  have hv := coneVolume_pos n κ _ hn' hκ hr
  have hj := coneMoment_pos n κ _ hn' hκ hr
  unfold coneNormalizedMoment ConePerspective.normalizedMoment
  exact div_pos hj (mul_pos (by linarith) (Real.rpow_pos_of_pos hv _))

theorem profile_eq_coneNormalizedMoment (n : ℕ) (hn : 2 ≤ n)
    (κ : ℝ) (hκ : 0 < κ)
    {u : ℝ} (hu : u ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2))) :
    profile n (profileConstant n κ) (((n:ℝ)-1)*κ) u =
      coneNormalizedMoment n κ u ^ (-(n:ℝ)/2) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hr, he⟩ := inverseRadius_spec n hn _ (mul_pos (by linarith) hκ) hu
  have H := momentPerspective_eq_profile_at_angle n hn κ _ hκ hr
  rw [he] at H
  rw [← H, momentPerspective_eq_normalized n _ _ (by linarith)
    (coneVolume_pos n κ _ hn' hκ hr) (coneMoment_pos n κ _ hn' hκ hr)]
  rfl

/-- Conversion of a perspective bound into exactly the real-power
normalization used in the article. -/
theorem normalized_bound_of_perspective (n : ℕ) (hn : 2 ≤ n)
    (κ v j m u : ℝ) (hκ : 0 < κ) (hv : 0 < v) (hj : 0 < j) (hm : 0 < m)
    (hu : u ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2)))
    (h : momentPerspective n v j ≤
      m * profile n (profileConstant n κ) (((n:ℝ)-1)*κ) u) :
    m^(-2/(n:ℝ)) * coneNormalizedMoment n κ u ≤
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
  exact (Real.rpow_le_rpow_iff_of_neg hg' (mul_pos (Real.rpow_pos_of_pos hm _) hg)
    (by linarith)).mp h

/-- Finite Jensen assembly, prior to any geometric identification of the
positive numbers with volumes, moments, and facet solid angles. -/
theorem finite_perspective_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (n : ℕ) (hn : 2 ≤ n) (κ : ℝ) (hκ : 0 < κ) (v j ω : ι → ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hj : ∀ i ∈ s, 0 < j i)
    (hω : ∀ i ∈ s, ω i ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2)))
    (hp : ∀ i ∈ s, momentPerspective n (v i) (j i) ≤
      profile n (profileConstant n κ) (((n:ℝ)-1)*κ) (ω i)) :
    momentPerspective n (∑ i ∈ s, v i) (∑ i ∈ s, j i) ≤
      (s.card:ℝ)*profile n (profileConstant n κ) (((n:ℝ)-1)*κ)
        ((∑ i ∈ s, ω i)/(s.card:ℝ)) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hD : 0 < ((n:ℝ)-1)*κ := mul_pos (by linarith) hκ
  refine (momentPerspective_sum s hs n (by positivity) v j hv hj).trans
    ((Finset.sum_le_sum hp).trans ?_)
  apply profile_sum_le_card s hs n hn _ _ (profileConstant_pos n κ hn' hκ) hD ω
  intro i hi
  rw [radiusAngle_image_positive n hn _ hD]
  exact hω i hi

end D4.ConeAnalysis
