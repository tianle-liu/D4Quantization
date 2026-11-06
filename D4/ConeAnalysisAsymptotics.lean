import D4.ConeAnalysisLimits
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! The two explicit asymptotic equivalents stated in the cone-concavity proof. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Filter CircularCone Asymptotics
open scoped Topology

theorem radialProfile_equivalent_zero (d K : ℝ) (hd : 2≤d) :
    radialProfile d K ~[𝓝[>] (0:ℝ)] (fun r : ℝ => K*r^(d-1)) := by
  apply isEquivalent_iff_exists_eq_mul.mpr
  refine ⟨fun r : ℝ => (1+alpha d*r^2)^(-d/2),?_,?_⟩
  · have hc : ContinuousAt (fun r : ℝ => (1+alpha d*r^2)^(-d/2)) 0 := by
      apply ContinuousAt.rpow_const (by fun_prop)
      exact Or.inl (by norm_num)
    have hh := hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
    simpa only [zero_pow (by decide : 2≠0),mul_zero,add_zero,Real.one_rpow] using hh
  · exact Eventually.of_forall (fun r => by dsimp only [Pi.mul_apply,radialProfile]; ring)

theorem radialProfile_equivalent_top (d K : ℝ) (hd : 2≤d) :
    radialProfile d K ~[atTop] (fun r : ℝ => (K*(alpha d)^(-d/2))*r⁻¹) := by
  have hα := alpha_pos d hd
  have ha : (alpha d)^(-d/2)≠0 := (Real.rpow_pos_of_pos hα _).ne'
  apply isEquivalent_iff_exists_eq_mul.mpr
  refine ⟨fun r : ℝ => (r⁻¹^2+alpha d)^(-d/2)/(alpha d)^(-d/2),?_,?_⟩
  · have hc : ContinuousAt (fun t : ℝ => (t^2+alpha d)^(-d/2)/(alpha d)^(-d/2)) 0 := by
      apply ContinuousAt.div _ continuousAt_const ha
      apply ContinuousAt.rpow_const (by fun_prop)
      exact Or.inl (by simpa using hα.ne')
    have hh := hc.tendsto.comp tendsto_inv_atTop_zero
    simpa only [Function.comp_def,zero_pow (by decide : 2≠0),zero_add,div_self ha] using hh
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    rw [radialProfile_inverse_expression d K r hd hr]
    dsimp only [Pi.mul_apply]
    field_simp [ha]
    ring

theorem radialProfile_asymptotic_constants_positive (d K : ℝ) (hd : 2≤d) (hK : 0<K) :
    0<K ∧ 0<K*(alpha d)^(-d/2) :=
  ⟨hK,mul_pos hK (Real.rpow_pos_of_pos (alpha_pos d hd) _)⟩

end D4.ConeAnalysis
