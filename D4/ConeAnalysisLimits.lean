import D4.ConeAnalysisConcavity
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Analysis.SpecificLimits.Basic

/-! The two zero endpoint limits of the actual cone-angle profile. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Filter CircularCone
open scoped Topology

def inverseRadius (n : ℕ) (D u : ℝ) : ℝ :=
  Function.invFunOn (radiusAngle n D) (Ioi 0) u

theorem inverseRadius_spec (n : ℕ) (hn : 2 ≤ n) (D : ℝ) (hD : 0 < D)
    {u : ℝ} (hu : u ∈ Ioo 0 (angle n D (Real.pi/2))) :
    0 < inverseRadius n D u ∧ radiusAngle n D (inverseRadius n D u) = u := by
  have him : u ∈ radiusAngle n D '' Ioi 0 := by
    rwa [radiusAngle_image_positive n hn D hD]
  exact Function.invFunOn_pos him

theorem inverseRadius_lt_iff (n : ℕ) (hn : 2 ≤ n) (D : ℝ) (hD : 0 < D)
    {u r : ℝ} (hu : u ∈ Ioo 0 (angle n D (Real.pi/2))) (hr : 0 < r) :
    inverseRadius n D u < r ↔ u < radiusAngle n D r := by
  obtain ⟨hi, he⟩ := inverseRadius_spec n hn D hD hu
  have H := (radiusAngle_strictMonoOn n D hD).lt_iff_lt hi.le hr.le
  rw [he] at H
  exact H.symm

theorem lt_inverseRadius_iff (n : ℕ) (hn : 2 ≤ n) (D : ℝ) (hD : 0 < D)
    {u r : ℝ} (hu : u ∈ Ioo 0 (angle n D (Real.pi/2))) (hr : 0 < r) :
    r < inverseRadius n D u ↔ radiusAngle n D r < u := by
  obtain ⟨hi, he⟩ := inverseRadius_spec n hn D hD hu
  have H := (radiusAngle_strictMonoOn n D hD).lt_iff_lt hr.le hi.le
  rw [he] at H
  exact H.symm

theorem inverseRadius_tendsto_zero (n : ℕ) (hn : 2 ≤ n) (D : ℝ) (hD : 0 < D) :
    Tendsto (inverseRadius n D) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (angle_endpoint_pos n D hD)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (radiusAngle_pos n D ε hD hε)).filter_mono nhdsWithin_le_nhds]
    with u hu huW huε
  have hu' : u ∈ Ioo 0 (angle n D (Real.pi/2)) := ⟨hu, huW⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (inverseRadius_spec n hn D hD hu').1]
  exact (inverseRadius_lt_iff n hn D hD hu' hε).mpr huε

theorem inverseRadius_tendsto_top (n : ℕ) (hn : 2 ≤ n) (D : ℝ) (hD : 0 < D) :
    Tendsto (inverseRadius n D) (𝓝[<] (angle n D (Real.pi/2))) atTop := by
  apply tendsto_atTop.2
  intro b
  let r := max 1 (b+1)
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hbr : b < r := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hω : radiusAngle n D r ∈ Ioo 0 (angle n D (Real.pi/2)) := by
    rw [← radiusAngle_image_positive n hn D hD]
    exact ⟨r, hr, rfl⟩
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hω.2).filter_mono nhdsWithin_le_nhds] with u hu huω
  have hu' : u ∈ Ioo 0 (angle n D (Real.pi/2)) := ⟨hω.1.trans huω, hu⟩
  exact (hbr.trans ((lt_inverseRadius_iff n hn D hD hu' hr).mpr huω)).le

theorem radialProfile_continuous (d K : ℝ) (hd : 2 ≤ d) :
    Continuous (radialProfile d K) := by
  have hα := alpha_pos d hd
  have hp : Continuous (fun r : ℝ => r^(d-1)) :=
    continuous_id.rpow_const (fun r => Or.inr (by linarith))
  have hq : Continuous (fun r : ℝ => (1+alpha d*r^2)^(-d/2)) :=
    (by fun_prop : Continuous (fun r : ℝ => 1+alpha d*r^2)).rpow_const
      (fun r => Or.inl (by positivity))
  exact (continuous_const.mul hp).mul hq

theorem radialProfile_zero (d K : ℝ) (hd : 2 ≤ d) : radialProfile d K 0 = 0 := by
  simp [radialProfile, Real.zero_rpow (by linarith : d-1 ≠ 0)]

theorem radialProfile_inverse_expression (d K r : ℝ) (hd : 2 ≤ d) (hr : 0 < r) :
    radialProfile d K r = K * r⁻¹ * (r⁻¹^2 + alpha d)^(-d/2) := by
  have hα := alpha_pos d hd
  have hB : 0 < r⁻¹^2 + alpha d := by positivity
  have hfac : 1 + alpha d*r^2 = r^2 * (r⁻¹^2 + alpha d) := by
    field_simp [hr.ne']
  have hp : (r^2)^(-d/2) = r^(-d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
    congr 1
    ring
  unfold radialProfile
  rw [hfac, Real.mul_rpow (sq_nonneg r) hB.le, hp]
  calc
    K * r^(d-1) * (r^(-d) * (r⁻¹^2+alpha d)^(-d/2)) =
        K * (r^(d-1)*r^(-d)) * (r⁻¹^2+alpha d)^(-d/2) := by ring
    _ = _ := by rw [← Real.rpow_add hr, show d-1 + -d = -1 by ring, Real.rpow_neg_one]

theorem radialProfile_tendsto_top (d K : ℝ) (hd : 2 ≤ d) :
    Tendsto (radialProfile d K) atTop (𝓝 0) := by
  have hα := alpha_pos d hd
  have hc : ContinuousAt (fun t : ℝ => K*t*(t^2+alpha d)^(-d/2)) 0 := by
    apply ContinuousAt.mul (by fun_prop)
    exact (by fun_prop : ContinuousAt (fun t : ℝ => t^2+alpha d) 0).rpow_const
      (Or.inl (by simpa using hα.ne'))
  have H := hc.tendsto.comp tendsto_inv_atTop_zero
  have he : (fun r : ℝ => K*r⁻¹*(r⁻¹^2+alpha d)^(-d/2)) =ᶠ[atTop]
      radialProfile d K := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact (radialProfile_inverse_expression d K r hd hr).symm
  have H' : Tendsto (fun r : ℝ => K*r⁻¹*(r⁻¹^2+alpha d)^(-d/2)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using H
  exact H'.congr' he

theorem profile_tendsto_zero (n : ℕ) (hn : 2 ≤ n) (K D : ℝ) (hD : 0 < D) :
    Tendsto (profile n K D) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have H := (radialProfile_continuous n K hn').continuousAt.tendsto.comp
    (inverseRadius_tendsto_zero n hn D hD)
  simpa only [radialProfile_zero n K hn', profile, reparametrize, inverseRadius,
    Function.comp_def] using H

theorem profile_tendsto_endpoint (n : ℕ) (hn : 2 ≤ n) (K D : ℝ) (hD : 0 < D) :
    Tendsto (profile n K D) (𝓝[<] (angle n D (Real.pi/2))) (𝓝 0) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  exact (radialProfile_tendsto_top n K hn').comp (inverseRadius_tendsto_top n hn D hD)

def closedProfile (n : ℕ) (K D : ℝ) : ℝ → ℝ :=
  extendFrom (Ioo 0 (angle n D (Real.pi/2))) (profile n K D)

theorem closedProfile_eq_profile (n : ℕ) (hn : 2 ≤ n) (K D : ℝ)
    (hK : 0 < K) (hD : 0 < D) {u : ℝ} (hu : u ∈ Ioo 0 (angle n D (Real.pi/2))) :
    closedProfile n K D u = profile n K D u :=
  extendFrom_extends (profile_continuousOn n hn K D hK hD) u hu

theorem closedProfile_continuousOn (n : ℕ) (hn : 2 ≤ n) (K D : ℝ)
    (hK : 0 < K) (hD : 0 < D) :
    ContinuousOn (closedProfile n K D) (Icc 0 (angle n D (Real.pi/2))) :=
  continuousOn_Icc_extendFrom_Ioo (angle_endpoint_pos n D hD).ne
    (profile_continuousOn n hn K D hK hD) (profile_tendsto_zero n hn K D hD)
    (profile_tendsto_endpoint n hn K D hD)

theorem closedProfile_zero (n : ℕ) (hn : 2 ≤ n) (K D : ℝ) (hD : 0 < D) :
    closedProfile n K D 0 = 0 :=
  eq_lim_at_left_extendFrom_Ioo (angle_endpoint_pos n D hD) (profile_tendsto_zero n hn K D hD)

theorem closedProfile_endpoint (n : ℕ) (hn : 2 ≤ n) (K D : ℝ) (hD : 0 < D) :
    closedProfile n K D (angle n D (Real.pi/2)) = 0 :=
  eq_lim_at_right_extendFrom_Ioo (angle_endpoint_pos n D hD)
    (profile_tendsto_endpoint n hn K D hD)

end D4.ConeAnalysis
