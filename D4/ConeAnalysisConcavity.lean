import D4.ConeAnalysis
import D4.ConeAnalysisParametric
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Continuous

/-! Strict concavity of the explicit circular-cone profile as a function
of its genuine angle integral, on the complete image of positive radii. -/
noncomputable section
namespace D4.ConeAnalysis
open Set CircularCone

def radialProfile (d K r : ℝ) : ℝ :=
  K * r ^ (d-1) * (1 + alpha d * r^2) ^ (-d/2)

def radialProfileDerivative (d K r : ℝ) : ℝ :=
  K * r ^ (d-2) * (1 + alpha d * r^2) ^ (-d/2-1) * (d-1-alpha d*r^2)

theorem hasDerivAt_radialProfile (d K r : ℝ) (hd : 2 ≤ d) (hr : 0 < r) :
    HasDerivAt (radialProfile d K) (radialProfileDerivative d K r) r := by
  have hα := alpha_pos d hd
  have hB : 0 < 1 + alpha d * r^2 := by positivity
  have hp := (hasDerivAt_id r).rpow_const (p := d-1) (Or.inl hr.ne')
  have hbase := (((hasDerivAt_id r).pow 2).const_mul (alpha d)).const_add 1
  have hq := hbase.rpow_const (p := -d/2) (Or.inl hB.ne')
  have hall := (hp.const_mul K).mul hq
  have hp1 : r ^ (d-1) = r ^ (d-2) * r := by
    rw [← Real.rpow_add_one hr.ne']
    congr 1
    ring
  have hp2 : (1+alpha d*r^2)^(-d/2) =
      (1+alpha d*r^2)^(-d/2-1) * (1+alpha d*r^2) := by
    rw [← Real.rpow_add_one hB.ne']
    congr 1
    ring
  convert hall using 1
  unfold radialProfileDerivative
  simp only [mul_one, one_mul, id_eq, Nat.reduceSub, pow_one]
  rw [show d-1-1 = d-2 by ring, hp1, hp2]
  ring

theorem profile_derivative_ratio (n : ℕ) (hn : 2 ≤ n) (K D r : ℝ)
    (hD : 0 < D) (hr : 0 < r) :
    radialProfileDerivative n K r =
      (K / D * CircularCone.slope n (r^2)) * (D * radiusKernel n r) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hα := alpha_pos n hn'
  have hX : 0 < 1+r^2 := by positivity
  have hpow : (1+r^2)^((n:ℝ)/2) * (1+r^2)^(-(n:ℝ)/2) = 1 := by
    rw [← Real.rpow_add hX]
    rw [show (n:ℝ)/2 + -(n:ℝ)/2 = 0 by ring, Real.rpow_zero]
  have hnat : (r:ℝ)^((n:ℝ)-2) = r^(n-2) := by
    rw [← Real.rpow_natCast, Nat.cast_sub hn]
    norm_num
  unfold radialProfileDerivative CircularCone.slope radiusKernel
  rw [hnat]
  have H := congrArg (fun z : ℝ => K * r^(n-2) *
    (1+alpha n*r^2)^(-(n:ℝ)/2-1) * ((n:ℝ)-1-alpha n*r^2) * z) hpow
  field_simp [hD.ne'] at H ⊢
  linear_combination -D * H

def profile (n : ℕ) (K D : ℝ) : ℝ → ℝ :=
  reparametrize (Ioi 0) (radiusAngle n D) (radialProfile n K)

@[simp] theorem profile_at_radius (n : ℕ) (K D r : ℝ) (hD : 0 < D) (hr : 0 < r) :
    profile n K D (radiusAngle n D r) = radialProfile n K r := by
  exact reparametrize_apply ((radiusAngle_strictMonoOn n D hD).mono Ioi_subset_Ici_self) hr

/-- The circular-cone profile is strictly concave in its actual solid-angle
parameter. All derivative and inverse-function premises are discharged. -/
theorem profile_strictConcave (n : ℕ) (hn : 2 ≤ n) (K D : ℝ)
    (hK : 0 < K) (hD : 0 < D) :
    StrictConcaveOn ℝ (radiusAngle n D '' Ioi 0) (profile n K D) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  apply strictConcaveOn_reparametrize (convex_Ioi (0:ℝ))
    (g := fun r => D * radiusKernel n r)
    (h := fun r => K / D * CircularCone.slope n (r^2))
    ((radiusAngle_strictMonoOn n D hD).mono Ioi_subset_Ici_self)
  · intro r hr
    exact (hasDerivAt_radiusAngle n D r).continuousAt.continuousWithinAt
  · intro r hr
    exact (hasDerivAt_radialProfile n K r hn' hr).continuousAt.continuousWithinAt
  · intro r hr
    exact hasDerivAt_radiusAngle n D r
  · intro r hr
    rw [← profile_derivative_ratio n hn K D r hD hr]
    exact hasDerivAt_radialProfile n K r hn' hr
  · intro r hr
    exact mul_pos hD (radiusKernel_pos n r hr)
  · intro r hr s hs hrs
    apply mul_lt_mul_of_pos_left _ (div_pos hK hD)
    apply slope_strictAntiOn n hn'
      (by change 0 < r^2; exact sq_pos_of_pos hr)
      (by change 0 < s^2; exact sq_pos_of_pos hs)
    exact (sq_lt_sq₀ (show 0 ≤ r from le_of_lt hr) (show 0 ≤ s from le_of_lt hs)).mpr hrs

/-- The finite equal-weight Jensen comparison for the actual cone profile. -/
theorem profile_sum_le_card {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (n : ℕ) (hn : 2 ≤ n) (K D : ℝ) (hK : 0 < K) (hD : 0 < D)
    (ω : ι → ℝ) (hω : ∀ i ∈ s, ω i ∈ radiusAngle n D '' Ioi 0) :
    (∑ i ∈ s, profile n K D (ω i)) ≤
      (s.card : ℝ) * profile n K D ((∑ i ∈ s, ω i) / s.card) := by
  have hc : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hw : ∑ i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    simp [Finset.sum_const, nsmul_eq_mul, hc.ne']
  have H := (profile_strictConcave n hn K D hK hD).concaveOn.le_map_sum
    (fun i hi => inv_nonneg.mpr hc.le) hw hω
  simp only [smul_eq_mul, ← Finset.mul_sum] at H
  have H' := mul_le_mul_of_nonneg_left H hc.le
  simpa [← mul_assoc, hc.ne', div_eq_mul_inv, mul_comm] using H'

theorem profile_strictConcave_interval (n : ℕ) (hn : 2 ≤ n) (K D : ℝ)
    (hK : 0 < K) (hD : 0 < D) :
    StrictConcaveOn ℝ (Ioo 0 (angle n D (Real.pi/2))) (profile n K D) := by
  rw [← radiusAngle_image_positive n hn D hD]
  exact profile_strictConcave n hn K D hK hD

theorem profile_continuousOn (n : ℕ) (hn : 2 ≤ n) (K D : ℝ)
    (hK : 0 < K) (hD : 0 < D) :
    ContinuousOn (profile n K D) (Ioo 0 (angle n D (Real.pi/2))) :=
  (profile_strictConcave_interval n hn K D hK hD).concaveOn.continuousOn isOpen_Ioo

end D4.ConeAnalysis
