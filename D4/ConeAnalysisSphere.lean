import D4.ConeAnalysisBound

/-! Strict comparison with the spherical lower bound, obtained directly
from the proved strict decrease of the cone slope. -/
noncomputable section
namespace D4.ConeAnalysis
open Set CircularCone

theorem slope_strictAntiOn_nonnegative (d : ℝ) (hd : 2 ≤ d) :
    StrictAntiOn (CircularCone.slope d) (Ici 0) := by
  have ha := alpha_pos d hd
  apply strictAntiOn_of_deriv_neg (convex_Ici (0:ℝ))
  · intro s hs
    have hs' : 0 ≤ s := hs
    apply ContinuousAt.continuousWithinAt
    unfold CircularCone.slope
    apply ContinuousAt.mul
    · apply ContinuousAt.mul (by fun_prop)
      exact (by fun_prop : ContinuousAt (fun s : ℝ => 1+s) s).rpow_const
        (Or.inl (by positivity))
    · exact (by fun_prop : ContinuousAt (fun s : ℝ => 1+alpha d*s) s).rpow_const
        (Or.inl (by positivity))
  · intro s hs
    have hs' : 0 < s := by simpa only [interior_Ici, mem_Ioi] using hs
    rw [(hasDerivAt_slope d s hd hs').deriv]
    exact slopeDerivative_neg d s hd hs'

theorem radialProfile_div_angle_lt (n : ℕ) (hn : 2 ≤ n) (K D r : ℝ)
    (hK : 0 < K) (hD : 0 < D) (hr : 0 < r) :
    radialProfile n K r / radiusAngle n D r < K/D*((n:ℝ)-1) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hω := radiusAngle_pos n D r hD hr
  obtain ⟨c, hc, he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
    (radialProfile n K) (radialProfileDerivative n K) hr
    (radialProfile_continuous n K hn').continuousOn
    (fun c hc => hasDerivAt_radialProfile n K c hn' hc.1)
    (radiusAngle n D) (fun c => D*radiusKernel n c)
    ((continuous_iff_continuousAt.mpr fun c =>
      (hasDerivAt_radiusAngle n D c).continuousAt).continuousOn)
    (fun c _ => hasDerivAt_radiusAngle n D c)
  rw [radialProfile_zero n K hn', radiusAngle_zero,
    sub_zero, sub_zero, profile_derivative_ratio n hn K D c hD hc.1] at he
  have he' : radialProfile n K r / radiusAngle n D r =
      K/D*CircularCone.slope n (c^2) := by
    apply (div_eq_iff hω.ne').mpr
    apply mul_right_cancel₀ (mul_pos hD (radiusKernel_pos n c hc.1)).ne'
    linear_combination -he
  rw [he']
  apply mul_lt_mul_of_pos_left _ (div_pos hK hD)
  have H := slope_strictAntiOn_nonnegative n hn' (show (0:ℝ) ∈ Ici 0 by simp)
    (sq_nonneg c) (sq_pos_of_pos hc.1)
  simpa only [CircularCone.slope, mul_zero, sub_zero, add_zero, Real.one_rpow, mul_one] using H

theorem profile_lt_spherePerspective (n : ℕ) (hn : 2 ≤ n)
    (κ : ℝ) (hκ : 0 < κ) {u : ℝ}
    (hu : u ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2))) :
    profile n (profileConstant n κ) (((n:ℝ)-1)*κ) u <
      ((n:ℝ)+2)^((n:ℝ)/2)/(n:ℝ)*u := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hD : 0 < ((n:ℝ)-1)*κ := mul_pos (by linarith) hκ
  obtain ⟨hr, he⟩ := inverseRadius_spec n hn _ hD hu
  have H := radialProfile_div_angle_lt n hn (profileConstant n κ) _ _
    (profileConstant_pos n κ hn' hκ) hD hr
  rw [he] at H
  have hprof := profile_at_radius n (profileConstant n κ) _ _ hD hr
  rw [he] at hprof
  rw [← hprof] at H
  have hconst : profileConstant n κ / (((n:ℝ)-1)*κ)*((n:ℝ)-1) =
      ((n:ℝ)+2)^((n:ℝ)/2)/(n:ℝ) := by
    unfold profileConstant
    field_simp
    ring
  rw [hconst] at H
  exact (div_lt_iff₀ hu.1).mp H

theorem coneNormalizedMoment_gt_sphere (n : ℕ) (hn : 2 ≤ n)
    (κ : ℝ) (hκ : 0 < κ) {u : ℝ}
    (hu : u ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2))) :
    ((n:ℝ)/u)^(2/(n:ℝ))/((n:ℝ)+2) < coneNormalizedMoment n κ u := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hn2 : 0 < (n:ℝ)+2 := by linarith
  have hb : 0 < ((n:ℝ)/u)^(2/(n:ℝ))/((n:ℝ)+2) :=
    div_pos (Real.rpow_pos_of_pos (div_pos hn0 hu.1) _) hn2
  have hp : (((n:ℝ)/u)^(2/(n:ℝ))/((n:ℝ)+2))^(-(n:ℝ)/2) =
      ((n:ℝ)+2)^((n:ℝ)/2)/(n:ℝ)*u := by
    rw [Real.div_rpow (Real.rpow_pos_of_pos (div_pos hn0 hu.1) _).le hn2.le,
      ← Real.rpow_mul (div_pos hn0 hu.1).le,
      show (2/(n:ℝ))*(-(n:ℝ)/2) = -1 by field_simp <;> ring,
      Real.rpow_neg_one, show -(n:ℝ)/2 = -((n:ℝ)/2) by ring,
      Real.rpow_neg hn2.le]
    field_simp
    ring
  have H := profile_lt_spherePerspective n hn κ hκ hu
  rw [profile_eq_coneNormalizedMoment n hn κ hκ hu, ← hp] at H
  exact (Real.rpow_lt_rpow_iff_of_neg (coneNormalizedMoment_pos n hn κ hκ hu) hb
    (by linarith)).mp H

end D4.ConeAnalysis
