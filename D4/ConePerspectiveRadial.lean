import D4.ConePerspectiveIntegral
import D4.ConeAnalysisComparison
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The complete two-Jensen comparison for a positive continuous radial
function on a compact probability space. All quantities in this theorem are
actual integrals of the explicit cone formulas. Identifying those integrals
with a geometric pyramid remains a separate polar-integration theorem. -/
noncomputable section
namespace D4.ConeAnalysis
open Set MeasureTheory ConePerspective CircularCone

theorem coneVolume_continuous (d κ : ℝ) (hd : 2 ≤ d) :
    Continuous (coneVolume d κ) := by
  exact continuous_const.mul (Real.continuous_rpow_const (by linarith))

theorem coneMoment_continuous (d κ : ℝ) (hd : 2 ≤ d) :
    Continuous (coneMoment d κ) := by
  exact (continuous_const.mul (coneVolume_continuous d κ hd)).mul
    (continuous_const.add (continuous_const.mul (continuous_id.pow 2)))

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

theorem radial_average_comparison {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (hn : 2 ≤ n)
    (κ : ℝ) (hκ : 0 < κ) (ρ : α → ℝ) (hρ : Continuous ρ) (hp : ∀ x, 0 < ρ x) :
    momentPerspective n (∫ x, coneVolume n κ (ρ x) ∂μ)
      (∫ x, coneMoment n κ (ρ x) ∂μ) ≤
    profile n (profileConstant n κ) (((n:ℝ)-1)*κ)
      (∫ x, radiusAngle n (((n:ℝ)-1)*κ) (ρ x) ∂μ) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  let K := profileConstant n κ
  let D := ((n:ℝ)-1)*κ
  have hK : 0 < K := profileConstant_pos n κ hn' hκ
  have hD : 0 < D := mul_pos (by linarith) hκ
  have cv := (coneVolume_continuous n κ hn').comp hρ
  have cj := (coneMoment_continuous n κ hn').comp hρ
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
  have H₁ := momentPerspective_integral μ n (min εv εj) (by positivity)
    (lt_min hεv hεj) _ _ (compact_integrable μ cv) (compact_integrable μ cj) hF
    (Filter.Eventually.of_forall fun x =>
      ⟨(min_le_left _ _).trans (hv x), (min_le_right _ _).trans (hj x)⟩)
  simp only [Function.comp_apply] at H₁
  rw [he] at H₁
  obtain ⟨xmin, _, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty cω.continuousOn
  obtain ⟨xmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty cω.continuousOn
  have hrange : ∀ x, radiusAngle n D (ρ x) ∈ Ioo 0 (angle n D (Real.pi/2)) := by
    intro x
    rw [← radiusAngle_image_positive n hn D hD]
    exact ⟨ρ x, hp x, rfl⟩
  exact H₁.trans (profile_integral μ n hn K D _ _ hK hD (hrange xmin).1
    (hrange xmax).2 _ (compact_integrable μ cω) (compact_integrable μ cp)
    (Filter.Eventually.of_forall fun x => ⟨hmin (mem_univ x), hmax (mem_univ x)⟩))

end D4.ConeAnalysis
