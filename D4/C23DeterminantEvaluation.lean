import D4.PolynomialDeterminants
import D4.PrincipalTreeWeights

noncomputable section
namespace D4.Secondary
open Certificate Principal

theorem determinantC2_extendWeight_eval (w : Fin 10 → ℝ) :
    eval (extendWeight w) CertificateMoments.determinantC2 =
      (secondaryForm cone2Vectors (w 0) (fun j => w j.succ)).det := by
  rw [determinantC2_eval]
  change (secondaryForm cone2Vectors (extendWeight w (0 : Fin 10).val)
    (fun j : Fin 9 => extendWeight w j.succ.val)).det = _
  simp only [extendWeight_fin]

theorem determinantC3_extendWeight_eval (w : Fin 10 → ℝ) :
    eval (extendWeight w) CertificateMoments.determinantC3 =
      (secondaryForm cone3Vectors (w 0) (fun j => w j.succ)).det := by
  rw [determinantC3_eval]
  change (secondaryForm cone3Vectors (extendWeight w (0 : Fin 10).val)
    (fun j : Fin 9 => extendWeight w j.succ.val)).det = _
  simp only [extendWeight_fin]

end D4.Secondary
