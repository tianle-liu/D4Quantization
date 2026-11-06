import D4.AreaFixedEnvelopeAnalytic
import D4.C23LocalCorrection

/-! Analyticity of the actual negative local branch along the C₁/C₂ path.
The compact window and spatial minimum are the concrete ones in the paper. -/
noncomputable section
namespace D4.C23Local
open Set MeasureTheory AreaEnvelope

theorem correction2_negative_analytic (p q r η R a₀ : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hη : 0 ≤ η) :
    AnalyticAt ℝ (fun a => negativeAreaIntegral {L : Plane | gap2 p q r L ≤ η}
      R (lower2 r) (gap2 p q r) (2*a)) a₀ := by
  have hU : Continuous (lower2 r) := by unfold lower2 min4; fun_prop
  exact (analyticAt_negativeAreaIntegral_fixed _
    (gap2_sublevel_compact p q r η hp hq hr hη) R (lower2 r) (gap2 p q r)
    hU.continuousOn (gap2_continuous p q r).continuousOn (2*a₀)).comp
      (analyticAt_const.mul analyticAt_id)

end D4.C23Local
