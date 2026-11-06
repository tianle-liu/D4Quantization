import D4.ConeAnalysisDimension
import D4.ConeAnalysisAssembly

/-! Exact evaluation of the two-dimensional six-facet constant. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory

theorem coneNormalizedMoment_at_radius (n : ℕ) (hn : 2 ≤ n) (κ r : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) :
    coneNormalizedMoment n κ (radiusAngle n (((n:ℝ)-1)*κ) r) =
      ConePerspective.normalizedMoment n (coneVolume n κ r) (coneMoment n κ r) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hD : 0 < ((n:ℝ)-1)*κ := mul_pos (by linarith) hκ
  have hu : radiusAngle n (((n:ℝ)-1)*κ) r ∈
      Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2)) := by
    rw [← radiusAngle_image_positive n hn _ hD]
    exact ⟨r, hr, rfl⟩
  obtain ⟨hi, he⟩ := inverseRadius_spec n hn _ hD hu
  have hrinv := (radiusAngle_strictMonoOn n (((n:ℝ)-1)*κ) hD).injOn hi.le hr.le he
  unfold coneNormalizedMoment
  rw [hrinv]

theorem angle_two (D θ : ℝ) : angle 2 D θ = D*θ := by
  simp [angle]

theorem radiusAngle_two_sqrt_three : radiusAngle 2 2 (1/Real.sqrt 3) = Real.pi/3 := by
  rw [radiusAngle_eq_angle_arctan 2 (by norm_num), ← Real.tan_pi_div_six,
    Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]), angle_two]
  ring

theorem coneNormalizedMoment_two_pi_div_three :
    coneNormalizedMoment 2 2 (Real.pi/3) = 5/(6*Real.sqrt 3) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have H := coneNormalizedMoment_at_radius 2 (by norm_num) 2 (1/Real.sqrt 3)
    (by norm_num) (div_pos zero_lt_one hs)
  norm_num only [Nat.cast_ofNat, show ((2:ℝ)-1)*2 = 2 by norm_num] at H
  rw [radiusAngle_two_sqrt_three] at H
  rw [H]
  norm_num [ConePerspective.normalizedMoment, coneVolume, coneMoment, CircularCone.alpha,
    Real.rpow_two]
  field_simp [hs.ne']
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

theorem hexagonal_value :
    (6:ℝ)^(-2/(2:ℝ))*coneNormalizedMoment 2 2 (Real.pi/3) = 5/(36*Real.sqrt 3) := by
  rw [coneNormalizedMoment_two_pi_div_three]
  norm_num
  ring

theorem dimensionBallVolume_one : dimensionBallVolume 1 = 2 := by
  unfold dimensionBallVolume
  rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_odd (k:=0) (by simp)]
  norm_num [Nat.doubleFactorial]

theorem dimensionBallVolume_two : dimensionBallVolume 2 = Real.pi := by
  unfold dimensionBallVolume
  rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_even (k:=1) (by simp)]
  norm_num [Real.pi_pos.le]

theorem dimension_two_bound_value :
    (2*(2^2-1):ℕ)^(-2/(2:ℝ)) *
      coneNormalizedMoment 2 (dimensionBallVolume (2-1))
        (((2:ℝ)*dimensionBallVolume 2)/(2*(2^2-1):ℕ)) = 5/(36*Real.sqrt 3) := by
  norm_num only [Nat.pow_two, Nat.mul_sub, Nat.mul_one, Nat.reduceMul,
    Nat.reduceSub, Nat.cast_ofNat]
  rw [dimensionBallVolume_one, dimensionBallVolume_two,
    show (2*Real.pi)/6 = Real.pi/3 by ring]
  simpa [Real.rpow_neg_one] using hexagonal_value

end D4.ConeAnalysis
