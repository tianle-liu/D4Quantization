import D4.ConeAnalysisSphereSupport
import Mathlib.Analysis.Convex.Integral

/-! Strict Jensen for the angular profile. The measure has full support,
so continuous nonconstant radial data cannot be almost everywhere constant. -/
noncomputable section
namespace D4.ConeAnalysis
open Set MeasureTheory MeasureTheory.Measure ConePerspective

theorem profile_integral_strict {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] (μ : Measure α) [IsProbabilityMeasure μ] [IsOpenPosMeasure μ]
    (n : ℕ) (hn : 2 ≤ n) (K D a b : ℝ) (hK : 0 < K) (hD : 0 < D)
    (ha : 0 < a) (hb : b < angle n D (Real.pi/2))
    (ω : α → ℝ) (hω : Continuous ω) (hi : Integrable ω μ)
    (hφ : Integrable (fun x => profile n K D (ω x)) μ)
    (hrange : ∀ x, ω x ∈ Icc a b) (hne : ∃ x y, ω x ≠ ω y) :
    (∫ x, profile n K D (ω x) ∂μ) < profile n K D (∫ x, ω x ∂μ) := by
  have hsub : Icc a b ⊆ Ioo 0 (angle n D (Real.pi/2)) := by
    intro u hu
    exact ⟨ha.trans_le hu.1, hu.2.trans_lt hb⟩
  have H := ((profile_strictConcave_interval n hn K D hK hD).subset hsub
    (convex_Icc a b)).ae_eq_const_or_lt_map_average
      ((profile_continuousOn n hn K D hK hD).mono hsub) isClosed_Icc
      (Filter.Eventually.of_forall hrange) hi hφ
  simp only [average_eq_integral, Function.comp_apply] at H
  rcases H with H | H
  · have he := eq_of_ae_eq H hω continuous_const
    obtain ⟨x, y, hxy⟩ := hne
    exact False.elim (hxy ((congrFun he x).trans (congrFun he y).symm))
  · exact H

private theorem compact_integrable {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (isClosed_tsupport f).isCompact

private theorem compact_positive_lower {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α] (f : α → ℝ) (hf : Continuous f)
    (hp : ∀ x, 0 < f x) : ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε ≤ f x := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  exact ⟨f x, hp x, fun y => hx (mem_univ y)⟩

theorem radial_perspective_le_average_profile {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (hn : 2 ≤ n)
    (κ : ℝ) (hκ : 0 < κ) (ρ : α → ℝ) (hρ : Continuous ρ) (hp : ∀ x, 0 < ρ x) :
    momentPerspective n (∫ x, coneVolume n κ (ρ x) ∂μ)
      (∫ x, coneMoment n κ (ρ x) ∂μ) ≤
      ∫ x, profile n (profileConstant n κ) (((n:ℝ)-1)*κ)
        (radiusAngle n (((n:ℝ)-1)*κ) (ρ x)) ∂μ := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  let K := profileConstant n κ
  let D := ((n:ℝ)-1)*κ
  have hD : 0 < D := mul_pos (by linarith) hκ
  have cv := (coneVolume_continuous n κ hn').comp hρ
  have cj := (coneMoment_continuous n κ hn').comp hρ
  have cp : Continuous (fun x => profile n K D (radiusAngle n D (ρ x))) := by
    have he : (fun x => profile n K D (radiusAngle n D (ρ x))) =
        fun x => radialProfile n K (ρ x) := by
      funext x
      exact profile_at_radius n K D (ρ x) hD (hp x)
    rw [he]
    exact (radialProfile_continuous n K hn').comp hρ
  have he : (fun x => momentPerspective n (coneVolume n κ (ρ x))
      (coneMoment n κ (ρ x))) =
      fun x => profile n K D (radiusAngle n D (ρ x)) := by
    funext x
    exact momentPerspective_eq_profile_at_angle n hn κ (ρ x) hκ (hp x)
  obtain ⟨εv, hεv, hv⟩ := compact_positive_lower _ cv
    (fun x => coneVolume_pos n κ (ρ x) hn' hκ (hp x))
  obtain ⟨εj, hεj, hj⟩ := compact_positive_lower _ cj
    (fun x => coneMoment_pos n κ (ρ x) hn' hκ (hp x))
  have hF : Integrable (fun x => momentPerspective n (coneVolume n κ (ρ x))
      (coneMoment n κ (ρ x))) μ := by
    rw [he]
    exact compact_integrable μ cp
  have H := momentPerspective_integral μ n (min εv εj) (by positivity)
    (lt_min hεv hεj) _ _ (compact_integrable μ cv) (compact_integrable μ cj) hF
    (Filter.Eventually.of_forall fun x =>
      ⟨(min_le_left _ _).trans (hv x), (min_le_right _ _).trans (hj x)⟩)
  simp only [Function.comp_apply] at H
  rw [he] at H
  exact H

theorem radial_average_comparison_strict {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] [IsOpenPosMeasure μ]
    (n : ℕ) (hn : 2 ≤ n) (κ : ℝ) (hκ : 0 < κ)
    (ρ : α → ℝ) (hρ : Continuous ρ) (hp : ∀ x, 0 < ρ x)
    (hne : ∃ x y, ρ x ≠ ρ y) :
    momentPerspective n (∫ x, coneVolume n κ (ρ x) ∂μ)
      (∫ x, coneMoment n κ (ρ x) ∂μ) <
    profile n (profileConstant n κ) (((n:ℝ)-1)*κ)
      (∫ x, radiusAngle n (((n:ℝ)-1)*κ) (ρ x) ∂μ) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  let K := profileConstant n κ
  let D := ((n:ℝ)-1)*κ
  have hK : 0 < K := profileConstant_pos n κ hn' hκ
  have hD : 0 < D := mul_pos (by linarith) hκ
  have cω : Continuous (fun x => radiusAngle n D (ρ x)) :=
    (continuous_iff_continuousAt.mpr fun r =>
      (hasDerivAt_radiusAngle n D r).continuousAt).comp hρ
  have cp : Continuous (fun x => profile n K D (radiusAngle n D (ρ x))) := by
    have he : (fun x => profile n K D (radiusAngle n D (ρ x))) =
        fun x => radialProfile n K (ρ x) := by
      funext x
      exact profile_at_radius n K D (ρ x) hD (hp x)
    rw [he]
    exact (radialProfile_continuous n K hn').comp hρ
  obtain ⟨xmin, _, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty cω.continuousOn
  obtain ⟨xmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty cω.continuousOn
  have hrange : ∀ x, radiusAngle n D (ρ x) ∈ Ioo 0 (angle n D (Real.pi/2)) := by
    intro x
    rw [← radiusAngle_image_positive n hn D hD]
    exact ⟨ρ x, hp x, rfl⟩
  have hne' : ∃ x y, radiusAngle n D (ρ x) ≠ radiusAngle n D (ρ y) := by
    obtain ⟨x, y, hxy⟩ := hne
    exact ⟨x, y, fun h => hxy ((radiusAngle_strictMonoOn n D hD).injOn (hp x).le (hp y).le h)⟩
  exact (radial_perspective_le_average_profile μ n hn κ hκ ρ hρ hp).trans_lt
    (profile_integral_strict μ n hn K D _ _ hK hD (hrange xmin).1 (hrange xmax).2
      _ cω (compact_integrable μ cω) (compact_integrable μ cp)
      (fun x => ⟨hmin (mem_univ x), hmax (mem_univ x)⟩) hne')

end D4.ConeAnalysis
