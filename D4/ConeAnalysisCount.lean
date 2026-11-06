import D4.ConeAnalysisBound

/-! Monotonicity of the fully normalized cone bound in the facet count. -/
noncomputable section
namespace D4.ConeAnalysis
open Set

theorem countConeBound_rpow (n : ℕ) (hn : 2 ≤ n) (κ A m : ℝ)
    (hκ : 0 < κ) (hm : 0 < m)
    (hu : A/m ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2))) :
    (m^(-2/(n:ℝ))*coneNormalizedMoment n κ (A/m))^(-(n:ℝ)/2) =
      m*profile n (profileConstant n κ) (((n:ℝ)-1)*κ) (A/m) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Real.mul_rpow (Real.rpow_nonneg hm.le _)
      (coneNormalizedMoment_pos n hn κ hκ hu).le,
    ← Real.rpow_mul hm.le,
    show (-2/(n:ℝ))*(-(n:ℝ)/2) = 1 by field_simp,
    Real.rpow_one, profile_eq_coneNormalizedMoment n hn κ hκ hu]

theorem countConeBound_antitone (n : ℕ) (hn : 2 ≤ n) (κ A m f : ℝ)
    (hκ : 0 < κ) (hA : 0 < A) (hm : 0 < m) (hmf : m ≤ f)
    (hu : A/m ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2))) :
    f^(-2/(n:ℝ))*coneNormalizedMoment n κ (A/f) ≤
      m^(-2/(n:ℝ))*coneNormalizedMoment n κ (A/m) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hf : 0 < f := hm.trans_le hmf
  have hfm : A/f ≤ A/m :=
    (div_le_div_iff₀ hf hm).mpr (mul_le_mul_of_nonneg_left hmf hA.le)
  have huf : A/f ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2)) :=
    ⟨div_pos hA hf, hfm.trans_lt hu.2⟩
  have H := count_profile_mono n hn (profileConstant n κ) (((n:ℝ)-1)*κ) A m f
    (profileConstant_pos n κ hn' hκ) (mul_pos (by linarith) hκ) hA hm hmf hu.2
  rw [← countConeBound_rpow n hn κ A m hκ hm hu,
    ← countConeBound_rpow n hn κ A f hκ hf huf] at H
  exact (Real.rpow_le_rpow_iff_of_neg
    (mul_pos (Real.rpow_pos_of_pos hm _) (coneNormalizedMoment_pos n hn κ hκ hu))
    (mul_pos (Real.rpow_pos_of_pos hf _) (coneNormalizedMoment_pos n hn κ hκ huf))
    (by linarith)).mp H

end D4.ConeAnalysis
