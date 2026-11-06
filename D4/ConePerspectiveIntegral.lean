import D4.ConePerspectiveProfile
import Mathlib.Analysis.Convex.Integral

/-! Probability-measure versions of the two Jensen steps used in the
pyramid comparison. The integrands are the concrete moment perspective
and the concrete cone-angle profile proved in the preceding modules. -/
noncomputable section
namespace D4.ConePerspective
open Set MeasureTheory

theorem momentPerspective_continuousOn (d : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => momentPerspective d q.1 q.2)
      (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := by
  intro q hq
  have hdiv : ContinuousAt (fun q : ℝ × ℝ => q.1 / q.2) q :=
    continuousAt_fst.div continuousAt_snd hq.2.ne'
  have hp := hdiv.rpow_const (p := 1+d/2) (Or.inl (div_pos hq.1 hq.2).ne')
  exact (continuousAt_const.mul (continuousAt_snd.mul hp)).continuousWithinAt

/-- The perspective Jensen inequality for positive, integrable data on a
probability space. A uniform positive lower bound supplies a closed domain. -/
theorem momentPerspective_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (d ε : ℝ) (hd : 0 ≤ d) (hε : 0 < ε)
    (v j : α → ℝ) (hv : Integrable v μ) (hj : Integrable j μ)
    (hF : Integrable (fun x => momentPerspective d (v x) (j x)) μ)
    (hb : ∀ᵐ x ∂μ, ε ≤ v x ∧ ε ≤ j x) :
    momentPerspective d (∫ x, v x ∂μ) (∫ x, j x ∂μ) ≤
      ∫ x, momentPerspective d (v x) (j x) ∂μ := by
  have hsub : Ici ε ×ˢ Ici ε ⊆ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := by
    intro q hq
    exact ⟨hε.trans_le hq.1, hε.trans_le hq.2⟩
  have H := ((momentPerspective_convex d hd).subset hsub
    ((convex_Ici ε).prod (convex_Ici ε))).map_integral_le
    ((momentPerspective_continuousOn d).mono hsub) (isClosed_Ici.prod isClosed_Ici)
    hb (hv.prodMk hj) hF
  simpa only [integral_pair hv hj] using H

end D4.ConePerspective

namespace D4.ConeAnalysis
open Set MeasureTheory

/-- Concave Jensen for the actual angle profile on any closed interval
strictly inside its domain. -/
theorem profile_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 2 ≤ n) (K D a b : ℝ) (hK : 0 < K) (hD : 0 < D)
    (ha : 0 < a) (hb : b < angle n D (Real.pi/2))
    (ω : α → ℝ) (hω : Integrable ω μ)
    (hφ : Integrable (fun x => profile n K D (ω x)) μ)
    (hrange : ∀ᵐ x ∂μ, ω x ∈ Icc a b) :
    (∫ x, profile n K D (ω x) ∂μ) ≤ profile n K D (∫ x, ω x ∂μ) := by
  have hsub : Icc a b ⊆ Ioo 0 (angle n D (Real.pi/2)) := by
    intro u hu
    exact ⟨ha.trans_le hu.1, hu.2.trans_lt hb⟩
  exact ((profile_strictConcave_interval n hn K D hK hD).concaveOn.subset hsub
    (convex_Icc a b)).le_map_integral
      ((profile_continuousOn n hn K D hK hD).mono hsub) isClosed_Icc hrange hω hφ

end D4.ConeAnalysis
