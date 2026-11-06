import D4.DualRemainderIntegral
import Mathlib.Analysis.Analytic.Constructions

/-! Analyticity of the genuine outside integral by exact cancellation of the
same independently computed correction in the total and local moments. -/
noncomputable section
namespace D4.Analytic
open Matrix MeasureTheory Set

theorem dualRemainder_analytic_of_matching_correction
    (Q : ℝ → Gram) (W : ℝ → Set Vec) (c : Vec) (t₀ : ℝ)
    (totalBase localBase correction : ℝ → ℝ)
    (htotal : AnalyticAt ℝ totalBase t₀) (hlocal : AnalyticAt ℝ localBase t₀)
    (hgeometry : ∀ᶠ t in nhds t₀,(Q t).PosDef ∧ IsCompact (W t) ∧
      ∀ x∈W t,∀ n : IntVec,x+dualMap (Q t) (castVec n)∈W t → n=0)
    (hN : ∀ᶠ t in nhds t₀,60*(Q t).det*moment (Q t)=totalBase t+correction t)
    (hW : ∀ᶠ t in nhds t₀,
      (15/4:ℝ)*(∫ r in W t,dualNearest (Q t) r)=localBase t+correction t) :
    AnalyticAt ℝ (fun t => ∫ r in dualRemainder (Q t) c (W t),dualNearest (Q t) r) t₀ := by
  apply ((htotal.sub hlocal).div analyticAt_const (by norm_num : (15/4:ℝ) ≠ 0)).congr
  filter_upwards [hgeometry,hN,hW] with t hg hn hw
  have he := dualRemainder_normalization hg.1 c (W t) hg.2.1 hg.2.2
  rw [hn,hw] at he
  apply (div_eq_iff (by norm_num : (15/4:ℝ) ≠ 0)).mpr
  dsimp only [Pi.sub_apply]
  linarith

end D4.Analytic
