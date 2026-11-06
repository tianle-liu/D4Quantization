import D4.ConePerspective
import D4.ConeAnalysisConcavity

/-! Exact algebraic identification of the circular-cone volume/moment
formulas with the strictly concave angle profile. Geometric integration
of a cone is a separate obligation; the formulas here are explicit. -/
noncomputable section
namespace D4.ConeAnalysis
open CircularCone ConePerspective

def coneVolume (d κ r : ℝ) : ℝ := κ / d * r^(d-1)

def coneMoment (d κ r : ℝ) : ℝ :=
  d / (d+2) * coneVolume d κ r * (1 + alpha d * r^2)

def profileConstant (d κ : ℝ) : ℝ := (d+2)^(d/2) * κ / d

theorem coneVolume_pos (d κ r : ℝ) (hd : 2 ≤ d) (hκ : 0 < κ) (hr : 0 < r) :
    0 < coneVolume d κ r := by
  unfold coneVolume
  exact mul_pos (div_pos hκ (by linarith)) (Real.rpow_pos_of_pos hr _)

theorem coneMoment_pos (d κ r : ℝ) (hd : 2 ≤ d) (hκ : 0 < κ) (hr : 0 < r) :
    0 < coneMoment d κ r := by
  have hα := alpha_pos d hd
  unfold coneMoment
  exact mul_pos (mul_pos (div_pos (by linarith) (by linarith))
    (coneVolume_pos d κ r hd hκ hr)) (by positivity)

theorem profileConstant_pos (d κ : ℝ) (hd : 2 ≤ d) (hκ : 0 < κ) :
    0 < profileConstant d κ := by
  unfold profileConstant
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _) hκ) (by linarith)

theorem momentPerspective_coneProfile (d κ r : ℝ)
    (hd : 2 ≤ d) (hκ : 0 < κ) (hr : 0 < r) :
    momentPerspective d (coneVolume d κ r) (coneMoment d κ r) =
      radialProfile d (profileConstant d κ) r := by
  have hd0 : 0 < d := by linarith
  have hd2 : 0 < d+2 := by linarith
  have hα := alpha_pos d hd
  have hB : 0 < 1+alpha d*r^2 := by positivity
  have hv := coneVolume_pos d κ r hd hκ hr
  have hm : coneMoment d κ r = (d/(d+2)*(1+alpha d*r^2)) * coneVolume d κ r := by
    unfold coneMoment
    ring
  rw [hm, momentPerspective_of_ratio d _ _ hv (mul_pos (div_pos hd0 hd2) hB),
    Real.mul_rpow (div_pos hd0 hd2).le hB.le, Real.div_rpow hd0.le hd2.le]
  unfold coneVolume radialProfile profileConstant
  rw [show -d/2 = -(d/2) by ring, Real.rpow_neg hB.le]
  field_simp [hd0.ne', (Real.rpow_pos_of_pos hd0 (d/2)).ne',
    (Real.rpow_pos_of_pos hd2 (d/2)).ne', (Real.rpow_pos_of_pos hB (d/2)).ne']
  ring

theorem momentPerspective_eq_profile_at_angle (n : ℕ) (hn : 2 ≤ n)
    (κ r : ℝ) (hκ : 0 < κ) (hr : 0 < r) :
    momentPerspective n (coneVolume n κ r) (coneMoment n κ r) =
      profile n (profileConstant n κ) (((n:ℝ)-1)*κ)
        (radiusAngle n (((n:ℝ)-1)*κ) r) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  rw [profile_at_radius n _ _ r (mul_pos (by linarith) hκ) hr]
  exact momentPerspective_coneProfile n κ r hn' hκ hr

end D4.ConeAnalysis
