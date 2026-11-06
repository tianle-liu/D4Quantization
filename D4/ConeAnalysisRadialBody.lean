import D4.ConeAnalysisPolar
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Polar integration over actual radial subsets of a finite-dimensional
space. The origin is omitted in the definition; it has Haar measure zero. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory MeasureTheory.Measure

def radialBody {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : sphere (0:E) 1 → ℝ) : Set E :=
  Subtype.val '' ((homeomorphUnitSphereProd E) ⁻¹'
    {p : sphere (0:E) 1 × Ioi (0:ℝ) | p.2.1 < ρ p.1})

theorem radialBody_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ρ : sphere (0:E) 1 → ℝ) (hρ : Measurable ρ) :
    MeasurableSet (radialBody ρ) := by
  apply (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0:E)).compl).measurableSet_image'
  exact (homeomorphUnitSphereProd E).measurable
    (measurableSet_lt (measurable_subtype_coe.comp measurable_snd) (hρ.comp measurable_fst))

theorem mem_radialBody_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : sphere (0:E) 1 → ℝ) (u : sphere (0:E) 1) (r : Ioi (0:ℝ)) :
    r.1 • u.1 ∈ radialBody ρ ↔ r.1 < ρ u := by
  constructor
  · rintro ⟨x, hx, he⟩
    have hx' : x = (homeomorphUnitSphereProd E).symm (u,r) := Subtype.ext he
    subst x
    simpa only [mem_preimage, Homeomorph.apply_symm_apply, mem_setOf_eq] using hx
  · intro h
    refine ⟨(homeomorphUnitSphereProd E).symm (u,r), ?_, rfl⟩
    simpa only [mem_preimage, Homeomorph.apply_symm_apply, mem_setOf_eq] using h

private def radialIndicator {E : Type*} [NormedAddCommGroup E]
    (p : ℕ) (ρ : sphere (0:E) 1 → ℝ) (q : sphere (0:E) 1 × Ioi (0:ℝ)) : ℝ :=
  if q.2.1 < ρ q.1 then q.2.1^p else 0

private theorem radialIndicator_integrable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℕ)
    (ρ : sphere (0:E) 1 → ℝ) (hρ : Measurable ρ)
    (M : ℝ) (hM : 0 < M) (hb : ∀ u, ρ u ≤ M) :
    Integrable (radialIndicator p ρ)
      (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1))) := by
  let S : Set (sphere (0:E) 1 × Ioi (0:ℝ)) := univ ×ˢ Iio ⟨M,hM⟩
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Iio
  have hfin : (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1))) S ≠ ⊤ := by
    rw [Measure.prod_prod, volumeIoiPow_apply_Iio]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hmeas : Measurable (radialIndicator p ρ) := by
    exact ((measurable_subtype_coe.comp measurable_snd).pow_const p).piecewise
      (measurableSet_lt (measurable_subtype_coe.comp measurable_snd) (hρ.comp measurable_fst))
      measurable_const
  have hint : IntegrableOn (radialIndicator p ρ) S
      (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1))) := by
    apply Measure.integrableOn_of_bounded hfin hmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun q => by
      unfold radialIndicator
      split_ifs with h
      · rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg q.2.2.le p)]
        exact pow_le_pow_left₀ q.2.2.le (h.le.trans (hb q.1)) p
      · simp only [norm_zero]
        exact pow_nonneg hM.le p
  apply (integrableOn_iff_integrable_of_support_subset (s:=S) ?_).mp hint
  intro q hq
  have h : q.2.1 < ρ q.1 := by
    by_contra hn
    exact hq (by simp [radialIndicator, hn])
  exact ⟨mem_univ _, h.trans_le (hb q.1)⟩

theorem integral_volumeIoiPow_truncated (k p : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (∫ r : Ioi (0:ℝ), (if r.1 < R then r.1^p else 0) ∂volumeIoiPow k) =
      R^(k+p+1)/(k+p+1) := by
  simp only [volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    (measurable_subtype_coe.pow_const k).real_toNNReal,
    integral_subtype_comap measurableSet_Ioi
      (fun r : ℝ => Real.toNNReal (r^k) • (if r < R then r^p else 0))]
  have he : (∫ r in Ioi (0:ℝ), Real.toNNReal (r^k) • (if r < R then r^p else 0)) =
      ∫ r in Ioi (0:ℝ), (Iio R).indicator (fun r => r^(k+p)) r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le k)]
    by_cases h : r < R <;> simp [Set.indicator, h, smul_eq_mul, pow_add]
  rw [he, setIntegral_indicator measurableSet_Iio]
  change (∫ r in Ioo (0:ℝ) R, r^(k+p)) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR, integral_pow]
  simp

/-- Full polar integration for every bounded positive measurable radial
function, with no geometric integration identity supplied as a premise. -/
theorem integral_norm_pow_radialBody {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℕ)
    (ρ : sphere (0:E) 1 → ℝ) (hρ : Measurable ρ)
    (hp : ∀ u, 0 < ρ u) (M : ℝ) (hM : 0 < M) (hb : ∀ u, ρ u ≤ M) :
    (∫ x in radialBody ρ, ‖x‖^p ∂μ) =
      (∫ u, ρ u^(Module.finrank ℝ E+p) ∂μ.toSphere) / (Module.finrank ℝ E+p) := by
  rw [← integral_indicator (radialBody_measurable ρ hρ), integral_polar_product μ]
  have he : (fun q : sphere (0:E) 1 × Ioi (0:ℝ) =>
      (radialBody ρ).indicator (fun x => ‖x‖^p) (q.2.1 • q.1.1)) =
      radialIndicator p ρ := by
    funext q
    have hu : ‖q.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp q.1.2
    have hr : 0 < q.2.1 := q.2.2
    simp only [Set.indicator, mem_radialBody_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr, hu, mul_one, radialIndicator]
  rw [he, integral_prod _ (radialIndicator_integrable μ p ρ hρ M hM hb)]
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hexp : Module.finrank ℝ E-1+p+1 = Module.finrank ℝ E+p := by omega
  have hi : (fun u => ∫ r : Ioi (0:ℝ), radialIndicator p ρ (u,r)
      ∂volumeIoiPow (Module.finrank ℝ E-1)) =
      fun u => ρ u^(Module.finrank ℝ E+p)/(Module.finrank ℝ E+p) := by
    funext u
    rw [show (fun r : Ioi (0:ℝ) => radialIndicator p ρ (u,r)) =
      (fun r => if r.1 < ρ u then r.1^p else 0) from rfl,
      integral_volumeIoiPow_truncated _ p (ρ u) (hp u).le, hexp]
    congr 1
    norm_num only [Nat.cast_add, Nat.cast_sub hn, Nat.cast_one]
    ring
  rw [hi]
  simp only [div_eq_mul_inv, integral_mul_const]

theorem integral_volumeIoiPow_truncated_function (k : ℕ) (R : ℝ) (f : ℝ → ℝ) :
    (∫ r : Ioi (0:ℝ), (if r.1 < R then f r.1 else 0) ∂volumeIoiPow k) =
      ∫ r in Ioo (0:ℝ) R, r^k*f r := by
  simp only [volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    (measurable_subtype_coe.pow_const k).real_toNNReal,
    integral_subtype_comap measurableSet_Ioi
      (fun r : ℝ => Real.toNNReal (r^k) • (if r < R then f r else 0))]
  have he : (∫ r in Ioi (0:ℝ), Real.toNNReal (r^k) • (if r < R then f r else 0)) =
      ∫ r in Ioi (0:ℝ), (Iio R).indicator (fun r => r^k*f r) r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le k)]
    by_cases h : r < R <;> simp [Set.indicator, h, smul_eq_mul]
  rw [he, setIntegral_indicator measurableSet_Iio]
  rfl

theorem integral_radialBody_radial {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ρ : sphere (0:E) 1 → ℝ) (hρ : Measurable ρ)
    (M : ℝ) (hM : 0 < M) (hb : ∀ u, ρ u ≤ M) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in radialBody ρ, f ‖x‖ ∂μ) =
      ∫ u, (∫ r in Ioo (0:ℝ) (ρ u), r^(Module.finrank ℝ E-1)*f r) ∂μ.toSphere := by
  let g : sphere (0:E) 1 × Ioi (0:ℝ) → ℝ :=
    fun q => if q.2.1 < ρ q.1 then f q.2.1 else 0
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) M).Nonempty from ⟨0, le_rfl, hM.le⟩) hf.norm.continuousOn
  have hg : Integrable g (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1))) := by
    apply ((radialIndicator_integrable μ 0 ρ hρ M hM hb).const_mul ‖f z‖).mono'
    · exact ((hf.measurable.comp (measurable_subtype_coe.comp measurable_snd)).piecewise
        (measurableSet_lt (measurable_subtype_coe.comp measurable_snd) (hρ.comp measurable_fst))
        measurable_const).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun q => by
        dsimp [g, radialIndicator]
        split_ifs with h
        · simp only [pow_zero, mul_one]
          exact hmax ⟨q.2.2.le, h.le.trans (hb q.1)⟩
        · simp
  rw [← integral_indicator (radialBody_measurable ρ hρ), integral_polar_product μ]
  have he : (fun q : sphere (0:E) 1 × Ioi (0:ℝ) =>
      (radialBody ρ).indicator (fun x => f ‖x‖) (q.2.1 • q.1.1)) = g := by
    funext q
    have hu : ‖q.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp q.1.2
    have hr : 0 < q.2.1 := q.2.2
    simp only [Set.indicator, mem_radialBody_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr, hu, mul_one, g]
  rw [he, integral_prod _ hg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u =>
    integral_volumeIoiPow_truncated_function _ (ρ u) f

end D4.ConeAnalysis
