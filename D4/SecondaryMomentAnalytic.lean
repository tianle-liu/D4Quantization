import D4.ConeParameterAnalytic
import D4.SecondaryClosedMoment

/-! The actual moments are jointly real analytic in all ten positive
parameters on each secondary cone. -/
noncomputable section
namespace D4.ConeParameterAnalytic
open Analytic Principal Secondary CertificateMoments

theorem secondary2_moment_analytic (w : Weights) (hw : ∀ i,0<w i) :
    AnalyticAt ℝ (fun x : Weights =>
      moment (secondaryForm cone2Vectors (x 0) (fun j => x j.succ))) w := by
  apply moment_analytic_of_formula _ momentC2 60 (by norm_num) w hw
    (secondary_entry_analytic cone2Vectors w)
  · exact fun _ hx => secondary_posDef_of_pos cone2Vectors (hx 0) (fun j => (hx j.succ).le)
  · exact c2_moment_identity_positive

theorem secondary3_moment_analytic (w : Weights) (hw : ∀ i,0<w i) :
    AnalyticAt ℝ (fun x : Weights =>
      moment (secondaryForm cone3Vectors (x 0) (fun j => x j.succ))) w := by
  apply moment_analytic_of_formula _ momentC3 60 (by norm_num) w hw
    (secondary_entry_analytic cone3Vectors w)
  · exact fun _ hx => secondary_posDef_of_pos cone3Vectors (hx 0) (fun j => (hx j.succ).le)
  · exact c3_moment_identity_positive

end D4.ConeParameterAnalytic
