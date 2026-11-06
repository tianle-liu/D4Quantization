import D4.ConeAnalysisSphere

/-! The facet-count constant is strictly stronger than the sphere bound. -/
noncomputable section
namespace D4.ConeAnalysis
open Set

theorem facet_bound_gt_sphere (n : ℕ) (hn : 2 ≤ n) (κ A m : ℝ)
    (hκ : 0 < κ) (hA : 0 < A) (hm : 0 < m)
    (hu : A/m ∈ Ioo 0 (angle n (((n:ℝ)-1)*κ) (Real.pi/2))) :
    ((n:ℝ)/A)^(2/(n:ℝ))/((n:ℝ)+2) <
      m^(-2/(n:ℝ))*coneNormalizedMoment n κ (A/m) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have H := mul_lt_mul_of_pos_left (coneNormalizedMoment_gt_sphere n hn κ hκ hu)
    (Real.rpow_pos_of_pos hm (-2/(n:ℝ)))
  have he : m^(-2/(n:ℝ))*(((n:ℝ)/(A/m))^(2/(n:ℝ))/((n:ℝ)+2)) =
      ((n:ℝ)/A)^(2/(n:ℝ))/((n:ℝ)+2) := by
    rw [show (n:ℝ)/(A/m) = ((n:ℝ)/A)*m by field_simp,
      Real.mul_rpow (div_pos hn0 hA).le hm.le, ← mul_div_assoc,
      mul_left_comm (m^(-2/(n:ℝ))),
      ← Real.rpow_add hm, show -2/(n:ℝ)+2/(n:ℝ) = 0 by ring,
      Real.rpow_zero, mul_one]
  rwa [he] at H

end D4.ConeAnalysis
