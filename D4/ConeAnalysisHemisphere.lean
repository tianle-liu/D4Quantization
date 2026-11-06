import D4.ConeAnalysisDimension
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! The angular endpoint is exactly half the total spherical measure.
The proof uses the two-step recurrences for Euclidean ball volumes and
the genuine sine-power integrals. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory Real

theorem dimensionBallVolume_gamma {k : ℕ} (hk : 0 < k) :
    dimensionBallVolume k = Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1) := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  simp only [dimensionBallVolume, measureReal_def, EuclideanSpace.volume_ball,
    Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]

theorem dimensionBallVolume_step {k : ℕ} (hk : 0 < k) :
    ((k : ℝ) + 2) * dimensionBallVolume (k + 2) = 2 * Real.pi * dimensionBallVolume k := by
  rw [dimensionBallVolume_gamma hk, dimensionBallVolume_gamma (by omega : 0 < k + 2)]
  have he : ((k + 2 : ℕ) : ℝ) / 2 + 1 = ((k : ℝ) / 2 + 1) + 1 := by push_cast; ring
  rw [he, Real.Gamma_add_one (by positivity), pow_add, Real.sq_sqrt Real.pi_nonneg]
  have hg : Real.Gamma ((k : ℝ) / 2 + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hk0 : (k : ℝ) / 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem dimensionBallVolume_one : dimensionBallVolume 1 = 2 := by
  have h := InnerProductSpace.volume_ball_of_dim_odd (E := EuclideanSpace ℝ (Fin 1))
    (k := 0) (by simp) 0 1
  norm_num [Nat.doubleFactorial] at h
  simpa only [dimensionBallVolume, measureReal_def, h, ENNReal.toReal_ofNat] using (rfl : (2 : ℝ) = 2)

theorem dimensionBallVolume_two : dimensionBallVolume 2 = Real.pi := by
  simp only [dimensionBallVolume, measureReal_def, EuclideanSpace.volume_ball_fin_two,
    ENNReal.ofReal_one, one_pow, one_mul, mul_one, ENNReal.toReal_ofReal Real.pi_pos.le]

theorem dimensionBallVolume_three : dimensionBallVolume 3 = 4 * Real.pi / 3 := by
  have h := dimensionBallVolume_step (k := 1) (by norm_num)
  rw [dimensionBallVolume_one] at h
  norm_num at h
  linarith

theorem sine_power_integral_step (k : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi, Real.sin t ^ (k + 2)) =
      ((k : ℝ) + 1) / ((k : ℝ) + 2) * ∫ t in (0 : ℝ)..Real.pi, Real.sin t ^ k := by
  rw [integral_sin_pow]
  simp only [Real.sin_zero, Real.sin_pi, zero_pow (by omega : k + 1 ≠ 0), zero_mul,
    sub_self, zero_div, zero_add]

theorem sine_power_integral_half (k : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi, Real.sin t ^ k) =
      2 * ∫ t in (0 : ℝ)..(Real.pi / 2), Real.sin t ^ k := by
  have hc := (Real.continuous_sin.pow k)
  have h := intervalIntegral.integral_comp_sub_left (a := Real.pi / 2) (b := Real.pi)
    (fun t => Real.sin t ^ k) Real.pi
  simp only [Real.sin_pi_sub, sub_self, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at h
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (Real.pi / 2))
    (hc.intervalIntegrable (Real.pi / 2) Real.pi), h]
  ring

theorem ballVolume_sine_integral (k : ℕ) :
    ((k : ℝ) + 1) * dimensionBallVolume (k + 1) *
      (∫ t in (0 : ℝ)..Real.pi, Real.sin t ^ k) =
        ((k : ℝ) + 2) * dimensionBallVolume (k + 2) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [dimensionBallVolume_one, dimensionBallVolume_two]
  | one =>
    simp [dimensionBallVolume_two, dimensionBallVolume_three, integral_sin]
    ring
  | more k ih _ =>
    have h1 := dimensionBallVolume_step (k := k + 1) (by omega)
    have h2 := dimensionBallVolume_step (k := k + 2) (by omega)
    rw [sine_power_integral_step]
    push_cast at h1 h2 ⊢
    have hden : (k : ℝ) + 2 ≠ 0 := by positivity
    calc
      _ = (2 * Real.pi * dimensionBallVolume (k + 1)) *
          (((k : ℝ) + 1) / ((k : ℝ) + 2) * ∫ t in (0 : ℝ)..Real.pi, Real.sin t ^ k) := by
        rw [← h1]
        congr 2 <;> first | omega | ring
      _ = (2 * Real.pi / ((k : ℝ) + 2)) *
          (((k : ℝ) + 1) * dimensionBallVolume (k + 1) *
            ∫ t in (0 : ℝ)..Real.pi, Real.sin t ^ k) := by ring
      _ = 2 * Real.pi * dimensionBallVolume (k + 2) := by rw [ih]; field_simp; ring
      _ = _ := by rw [← h2]

theorem twice_halfAngle_eq_dimension_ballVolume {n : ℕ} (hn : 2 ≤ n) :
    2 * angle n (((n : ℝ) - 1) * dimensionBallVolume (n - 1)) (Real.pi / 2) =
      (n : ℝ) * dimensionBallVolume n := by
  have h := ballVolume_sine_integral (n - 2)
  have h1 : n - 2 + 1 = n - 1 := by omega
  have h2 : n - 2 + 2 = n := by omega
  rw [h1, h2, sine_power_integral_half] at h
  have hc : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_sub hn]; norm_num
  rw [hc] at h
  unfold angle
  nlinarith [h]

theorem twice_halfAngle_eq_ballVolume {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {z : E} (hz : z ≠ 0)
    (hd : 2 ≤ Module.finrank ℝ E) :
    2 * angle (Module.finrank ℝ E)
      ((Module.finrank ℝ (D4.FacetGeometry.tangent z) : ℝ) *
        volume.real (ball (0 : D4.FacetGeometry.tangent z) 1)) (Real.pi / 2) =
      (Module.finrank ℝ E : ℝ) * volume.real (ball (0 : E) 1) := by
  letI : Nontrivial E := ⟨⟨z, 0, hz⟩⟩
  rw [tangent_unitBall_volume hz hd, unitBall_volume_eq_dimension]
  have he : (Module.finrank ℝ (D4.FacetGeometry.tangent z) : ℝ) =
      (Module.finrank ℝ E : ℝ) - 1 := by
    have ht := D4.FacetGeometry.tangent_finrank hz
    have ht' : (Module.finrank ℝ (D4.FacetGeometry.tangent z) : ℝ) + 1 =
        (Module.finrank ℝ E : ℝ) := by exact_mod_cast ht
    linarith
  rw [he]
  exact twice_halfAngle_eq_dimension_ballVolume hd

end D4.ConeAnalysis
