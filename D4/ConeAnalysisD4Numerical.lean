import D4.GeometricTheoremBCorollaries
import D4.ParityMoment
import D4.EuclideanMoment
import D4.ConeAnalysisCount
import Mathlib.Data.Real.Pi.Bounds

/-! Exact rational estimates for the D4 comparison in the final paragraph.
No floating-point evaluation or unverified numerical oracle is used. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace D4.ConeAnalysis
open Set Metric MeasureTheory D4.FacetGeometry

theorem radiusAngle_four (r : ℝ) :
    radiusAngle 4 (4*Real.pi) r = 2*Real.pi*(Real.arctan r-r/(1+r^2)) := by
  rw [radiusAngle_eq_angle_arctan 4 (by norm_num)]
  unfold angle
  norm_num only [Nat.reduceSub]
  rw [integral_sin_sq]
  simp only [Real.sin_zero, Real.cos_zero, zero_mul, zero_sub, sub_zero,
    Real.sin_arctan, Real.cos_arctan]
  have hs : 0 < Real.sqrt (1+r^2) := Real.sqrt_pos.2 (by positivity)
  have he : Real.sqrt (1+r^2)^2 = 1+r^2 := Real.sq_sqrt (by positivity)
  field_simp
  nlinarith

theorem arctan_27_40_upper :
    Real.arctan (27/40:ℝ) - (27/40:ℝ)/(1+(27/40:ℝ)^2) < (3.14:ℝ)/24 := by
  let p : ℝ → ℝ := fun x => ∑ i ∈ Finset.range 7, (-1:ℝ)^i*x^(2*i)
  have hp : Continuous p := by
    unfold p
    fun_prop
  have hf : Continuous (fun x : ℝ => 1/(1+x^2)) :=
    continuous_const.div (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)
  have H := intervalIntegral.integral_mono_on (μ:=volume) (by norm_num : (0:ℝ) ≤ 27/40)
    (hf.intervalIntegrable _ _) (hp.intervalIntegrable _ _) (fun x hx => by
      apply (div_le_iff₀ (by positivity : 0 < 1+x^2)).mpr
      have he : p x * (1+x^2) = 1+x^14 := by norm_num [p, Finset.sum_range_succ]; ring
      rw [he]
      have hh : 0 ≤ x^14 := by positivity
      linarith)
  rw [integral_one_div_one_add_sq, Real.arctan_zero, sub_zero] at H
  have he : (∫ x in (0:ℝ)..(27/40:ℝ), p x) =
      ∑ i ∈ Finset.range 7, (-1:ℝ)^i*((27/40:ℝ)^(2*i+1)/(2*i+1)) := by
    simp only [p]
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp
    · intro i hi
      exact (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _
  rw [he] at H
  norm_num [Finset.sum_range_succ] at H ⊢
  linarith

theorem d4_angle_bracket :
    Real.pi^2/12 ∈ Icc (radiusAngle 4 (4*Real.pi) (27/40))
      (radiusAngle 4 (4*Real.pi) 1) := by
  rw [radiusAngle_four, radiusAngle_four, Real.arctan_one]
  constructor
  · have h := arctan_27_40_upper.trans (div_lt_div_of_pos_right Real.pi_gt_d2 (by norm_num))
    have hp := mul_lt_mul_of_pos_left h (show 0 < 2*Real.pi by positivity)
    nlinarith
  · norm_num
    nlinarith [Real.pi_gt_three]

theorem dimensionBallVolume_three : dimensionBallVolume 3 = 4*Real.pi/3 := by
  unfold dimensionBallVolume
  rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_odd (k:=1) (by simp)]
  norm_num [Nat.doubleFactorial, Real.pi_pos.le]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

theorem dimensionBallVolume_four : dimensionBallVolume 4 = Real.pi^2/2 := by
  unfold dimensionBallVolume
  rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_even (k:=2) (by simp)]
  norm_num [Real.pi_pos.le]
  positivity

theorem profile_four_d4_lower : (1200/169:ℝ) < profile 4 (12*Real.pi) (4*Real.pi) (Real.pi^2/12) := by
  have hD : 0 < 4*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hK : 0 < 12*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hmem (r : ℝ) (hr : 0 < r) : radiusAngle 4 (4*Real.pi) r ∈
      Ioo 0 (angle 4 (4*Real.pi) (Real.pi/2)) := by
    rw [← radiusAngle_image_positive 4 (by norm_num) _ hD]
    exact ⟨r, hr, rfl⟩
  have H := (profile_strictConcave_interval 4 (by norm_num) _ _ hK hD).concaveOn.min_le_of_mem_Icc
    (hmem (27/40) (by norm_num)) (hmem 1 zero_lt_one) d4_angle_bracket
  rw [profile_at_radius 4 _ _ _ hD (by norm_num : (0:ℝ) < 27/40),
    profile_at_radius 4 _ _ _ hD zero_lt_one] at H
  have h0 : (1200/169:ℝ) < radialProfile 4 (12*Real.pi) (27/40) := by
    norm_num [radialProfile, CircularCone.alpha, Real.rpow_neg, Real.rpow_natCast]
    nlinarith [Real.pi_gt_d2]
  have h1 : (1200/169:ℝ) < radialProfile 4 (12*Real.pi) 1 := by
    norm_num [radialProfile, CircularCone.alpha, Real.rpow_neg, Real.rpow_natCast]
    nlinarith [Real.pi_gt_d2]
  exact (lt_min h0 h1).trans_le H

theorem d4ConeAngle_mem : Real.pi^2/12 ∈ Ioo 0 (angle 4 (4*Real.pi) (Real.pi/2)) := by
  have hmem : radiusAngle 4 (4*Real.pi) 1 ∈ Ioo 0 (angle 4 (4*Real.pi) (Real.pi/2)) := by
    rw [← radiusAngle_image_positive 4 (by norm_num) _ (by positivity)]
    exact ⟨1, by norm_num, rfl⟩
  exact ⟨by positivity, d4_angle_bracket.2.trans_lt hmem.2⟩

theorem dimensionalConeBound_four (m : ℝ) : dimensionalConeBound 4 m =
    m^(-2/(4:ℝ))*coneNormalizedMoment 4 (4*Real.pi/3) ((2*Real.pi^2)/m) := by
  simp only [dimensionalConeBound, Nat.cast_ofNat, Nat.reduceSub,
    dimensionBallVolume_three, dimensionBallVolume_four]
  rw [show (4:ℝ)*(Real.pi^2/2) = 2*Real.pi^2 by ring]

theorem dimensionalConeBound_four_twentyFour_rpow :
    (dimensionalConeBound 4 24)^(-2:ℝ) =
      24*profile 4 (12*Real.pi) (4*Real.pi) (Real.pi^2/12) := by
  have hD : (((4:ℝ)-1)*(4*Real.pi/3)) = 4*Real.pi := by ring
  have hu : (2*Real.pi^2)/24 ∈
      Ioo 0 (angle 4 (((4:ℝ)-1)*(4*Real.pi/3)) (Real.pi/2)) := by
    rw [hD, show (2*Real.pi^2)/24 = Real.pi^2/12 by ring]
    exact d4ConeAngle_mem
  have H := countConeBound_rpow 4 (by norm_num) (4*Real.pi/3) (2*Real.pi^2) 24
    (by positivity) (by norm_num) hu
  simp only [Nat.cast_ofNat] at H
  rw [← dimensionalConeBound_four, hD] at H
  have hK : profileConstant 4 (4*Real.pi/3) = 12*Real.pi := by
    norm_num [profileConstant]
    ring
  norm_num only [Nat.cast_ofNat, show -(4:ℝ)/2 = -2 by norm_num] at H
  rw [hK, show (2*Real.pi^2)/24 = Real.pi^2/12 by ring] at H
  exact H

theorem dimensionalConeBound_four_twentyFour_pos : 0 < dimensionalConeBound 4 24 := by
  rw [dimensionalConeBound_four]
  apply mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
  apply coneNormalizedMoment_pos 4 (by norm_num) _ (by positivity)
  simp only [Nat.cast_ofNat]
  rw [show (((4:ℝ)-1)*(4*Real.pi/3)) = 4*Real.pi by ring,
    show (2*Real.pi^2)/24 = Real.pi^2/12 by ring]
  exact d4ConeAngle_mem

theorem dimensionalConeBound_four_twentyFour_lt_optimal :
    dimensionalConeBound 4 24 < D4.Analytic.optimalConstant := by
  have hpos := D4.Analytic.optimalConstant_pos
  have hp : D4.Analytic.optimalConstant^(-2:ℝ) = (28800/169:ℝ) := by
    rw [Real.rpow_neg hpos.le, Real.rpow_two]
    unfold D4.Analytic.optimalConstant
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hs0 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'
    field_simp
    nlinarith
  apply (Real.rpow_lt_rpow_iff_of_neg hpos dimensionalConeBound_four_twentyFour_pos
    (by norm_num : (-2:ℝ) < 0)).mp
  rw [hp, dimensionalConeBound_four_twentyFour_rpow]
  linarith [profile_four_d4_lower]

theorem d4_final_cone_chain :
    dimensionalConeBound 4 30 ≤ dimensionalConeBound 4 24 ∧
      dimensionalConeBound 4 24 < D4.Analytic.normalizedMoment (D4.gramMatrix ℝ) := by
  constructor
  · rw [dimensionalConeBound_four, dimensionalConeBound_four]
    apply countConeBound_antitone 4 (by norm_num) (4*Real.pi/3) (2*Real.pi^2) 24 30
      (by positivity) (by positivity) (by norm_num) (by norm_num)
    simp only [Nat.cast_ofNat]
    rw [show (((4:ℝ)-1)*(4*Real.pi/3)) = 4*Real.pi by ring,
      show (2*Real.pi^2)/24 = Real.pi^2/12 by ring]
    exact d4ConeAngle_mem
  · rw [D4.Quantizer.normalizedMoment_gramMatrix]
    exact dimensionalConeBound_four_twentyFour_lt_optimal

theorem d4_final_euclidean_cone_chain :
    dimensionalConeBound 4 30 ≤ dimensionalConeBound 4 24 ∧
      dimensionalConeBound 4 24 < D4.Euclidean.normalizedCellMoment (D4.basisMatrix ℝ) := by
  refine ⟨d4_final_cone_chain.1, ?_⟩
  rw [D4.Euclidean.normalizedCellMoment_eq (by rw [D4.det_basisMatrix]; norm_num),
    D4.Euclidean.gram, D4.basisMatrix_transpose_mul]
  exact d4_final_cone_chain.2

end D4.ConeAnalysis
