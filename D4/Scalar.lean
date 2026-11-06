import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-!
# The scalar comparison in arXiv:2611.00100v2

This file proves the full one-variable comparison, including strictness,
from the explicit affine bounds in the paper. The endpoint inequalities
are proved by rational arithmetic; convexity fills the entire intervals.
No lattice-classification or moment-formula premise is asserted here.
-/
namespace D4

/-- Raising the five-fourths power to the fourth power removes the real exponent. -/
theorem fiveFourths_pow_four (d : ℝ) (hd : 0 ≤ d) :
    (d ^ (5 / 4 : ℝ)) ^ (4 : ℕ) = d ^ (5 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd]
  norm_num
  exact Real.rpow_natCast d 5

/-- The same identity for the fourth root. -/
theorem quarter_pow_four (d : ℝ) (hd : 0 ≤ d) :
    (d ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = d := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd]
  norm_num

theorem fiveFourths_eq_mul_quarter (d : ℝ) (hd : 0 < d) :
    d ^ (5 / 4 : ℝ) = d * d ^ (1 / 4 : ℝ) := by
  have h := Real.rpow_add hd (1 : ℝ) (1 / 4 : ℝ)
  norm_num at h
  exact h

/-- A strictly larger fourth power certifies a strict endpoint comparison. -/
theorem endpoint_of_fourth_powers (k d v : ℝ) (hd : 0 ≤ d)
    (hv : 0 ≤ v) (h : k^4 * d^5 < v^4) : k * d ^ (5 / 4 : ℝ) < v := by
  apply lt_of_pow_lt_pow_left₀ 4 hv
  simpa only [mul_pow, fiveFourths_pow_four d hd] using h

/-- Convexity of the five-fourths power extends affine endpoint bounds.
The left endpoint is strict and the right endpoint may attain equality. -/
theorem affine_dominates_fiveFourths (k m c l r d : ℝ)
    (hk : 0 ≤ k) (hl : 0 ≤ l) (hlr : l < r)
    (hdl : l ≤ d) (hdr : d < r)
    (hleft : k * l ^ (5 / 4 : ℝ) < m*l+c)
    (hright : k * r ^ (5 / 4 : ℝ) ≤ m*r+c) :
    k * d ^ (5 / 4 : ℝ) < m*d+c := by
  let a : ℝ := (r-d)/(r-l)
  let b : ℝ := (d-l)/(r-l)
  have hden : 0 < r-l := sub_pos.mpr hlr
  have ha : 0 < a := div_pos (sub_pos.mpr hdr) hden
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hdl) hden.le
  have hab : a+b=1 := by dsimp [a,b]; field_simp
  have hdab : a*l+b*r=d := by dsimp [a,b]; field_simp; ring
  have hconv := (convexOn_rpow (by norm_num : (1 : ℝ) ≤ 5/4)).2
    hl (hl.trans hlr.le) ha.le hb hab
  simp only [smul_eq_mul, hdab] at hconv
  have hkc := mul_le_mul_of_nonneg_left hconv hk
  have hleft' := mul_lt_mul_of_pos_left hleft ha
  have hright' := mul_le_mul_of_nonneg_left hright hb
  have hsum : a*(m*l+c)+b*(m*r+c)=m*d+c := by
    calc
      _ = m*(a*l+b*r)+c*(a+b) := by ring
      _ = _ := by rw [hdab, hab]; ring
  nlinarith only [hkc, hleft', hright', hsum]

/-- Closed-interval version when both endpoint bounds are strict. -/
theorem affine_dominates_fiveFourths_closed (k m c l r d : ℝ)
    (hk : 0 ≤ k) (hl : 0 ≤ l) (hlr : l < r)
    (hdl : l ≤ d) (hdr : d ≤ r)
    (hleft : k * l ^ (5 / 4 : ℝ) < m*l+c)
    (hright : k * r ^ (5 / 4 : ℝ) < m*r+c) :
    k * d ^ (5 / 4 : ℝ) < m*d+c := by
  rcases eq_or_lt_of_le hdr with rfl | hdr
  · exact hright
  · exact affine_dominates_fiveFourths k m c l r d hk hl hlr hdl hdr hleft hright.le

/-- The low interval in the comparison for the second and third cones. -/
theorem c23_low (d : ℝ) (hd : 0 < d) (hdu : d ≤ 7/20) :
    104 * d ^ (5/4 : ℝ) < 80*d := by
  have hroot : d ^ (1/4 : ℝ) < 10/13 := by
    apply lt_of_pow_lt_pow_left₀ 4 (by norm_num : (0 : ℝ) ≤ 10/13)
    rw [quarter_pow_four d hd.le]
    linarith [show (7/20 : ℝ) < (10/13)^4 by norm_num]
  rw [fiveFourths_eq_mul_quarter d hd]
  nlinarith [mul_lt_mul_of_pos_left hroot hd]

/-- The two exact fourth-power checks for the middle affine function. -/
theorem c23_middle_endpoint_checks :
    (104 : ℝ)^4*(7/20)^5 < (1681/60)^4 ∧
    (104 : ℝ)^4*(133/200)^5 < (18737/300)^4 := by norm_num

/-- The exact lower-endpoint check for the final affine function. -/
theorem c23_high_endpoint_check :
    (104 : ℝ)^4*(133/200)^5 < (3123/50)^4 := by norm_num

/-- The middle interval, including both endpoints. -/
theorem c23_middle (d : ℝ) (hdl : 7/20 ≤ d) (hdu : d ≤ 133/200) :
    104 * d ^ (5/4 : ℝ) < (328/3)*d-41/4 := by
  change 104 * d ^ (5/4 : ℝ) < (328/3)*d + -(41/4)
  apply affine_dominates_fiveFourths_closed 104 (328/3) (-(41/4)) (7/20) (133/200) d
    (by norm_num) (by norm_num) (by norm_num) hdl hdu
  · apply endpoint_of_fourth_powers <;> norm_num
  · apply endpoint_of_fourth_powers <;> norm_num

/-- The final interval is strict below one. -/
theorem c23_high (d : ℝ) (hdl : 133/200 ≤ d) (hdu : d < 1) :
    104 * d ^ (5/4 : ℝ) < 124*d-20 := by
  apply affine_dominates_fiveFourths 104 124 (-20) (133/200) 1 d
    (by norm_num) (by norm_num) (by norm_num) hdl hdu
  · apply endpoint_of_fourth_powers <;> norm_num
  · norm_num

/-- Full strict scalar comparison for the second and third cones. -/
theorem c23_strict (d : ℝ) (hd : 0 < d) (hdu : d < 1) :
    104 * d ^ (5/4 : ℝ) < max (80*d) (max ((328/3)*d-41/4) (124*d-20)) := by
  by_cases hlow : d ≤ 7/20
  · exact (c23_low d hd hlow).trans_le (le_max_left _ _)
  · by_cases hmid : d ≤ 133/200
    · exact (c23_middle d (le_of_not_ge hlow) hmid).trans_le
        ((le_max_left _ _).trans (le_max_right _ _))
    · exact (c23_high d (le_of_not_ge hmid) hdu).trans_le
        ((le_max_right _ _).trans (le_max_right _ _))

/-- Non-strict comparison on the entire normalized determinant interval. -/
theorem c23_bound (d : ℝ) (hd : 0 < d) (hdu : d ≤ 1) :
    104 * d ^ (5/4 : ℝ) ≤ max (80*d) (max ((328/3)*d-41/4) (124*d-20)) := by
  rcases eq_or_lt_of_le hdu with rfl | hdu
  · norm_num
  · exact (c23_strict d hd hdu).le

/-- Equality in the scalar maximum occurs only at normalized determinant one. -/
theorem c23_equality_iff (d : ℝ) (hd : 0 < d) (hdu : d ≤ 1) :
    104 * d ^ (5/4 : ℝ) = max (80*d) (max ((328/3)*d-41/4) (124*d-20)) ↔ d=1 := by
  constructor
  · intro h
    by_contra hne
    exact (ne_of_lt (c23_strict d hd (lt_of_le_of_ne hdu hne))) h
  · rintro rfl
    norm_num

/-- The coefficient `48 c_*` in the first-cone comparison. -/
noncomputable def c1Factor : ℝ := 13 * Real.sqrt 2 / 5

theorem c1Factor_pos : 0 < c1Factor := by
  unfold c1Factor
  positivity

theorem c1Factor_pow_four : c1Factor^4 = 114244/625 := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  unfold c1Factor
  calc
    (13 * Real.sqrt 2 / 5)^4 = (13/5 : ℝ)^4 * ((Real.sqrt 2)^2)^2 := by ring
    _ = 114244/625 := by rw [hs]; norm_num

/-- The first-cone coefficient is exactly 48 times the claimed optimum. -/
theorem c1Factor_eq_target : c1Factor = 48 * (13 / (120 * Real.sqrt 2)) := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  unfold c1Factor
  field_simp
  nlinarith only [hs]

/-- All four exact endpoint checks for the first cone. -/
theorem c1_endpoint_checks :
    (114244/625 : ℝ)*(1/200)^5 < ((4/3)*(1/200)-7/4000)^4 ∧
    (114244/625 : ℝ)*(9/1000)^5 < ((4/3)*(9/1000)-7/4000)^4 ∧
    (114244/625 : ℝ)*(9/1000)^5 < ((3/2)*(9/1000)-33/10000)^4 ∧
    (114244/625 : ℝ)*(1/80)^5 < ((3/2)*(1/80)-33/10000)^4 := by norm_num

/-- The small-determinant comparison for the first cone. -/
theorem c1_low (d : ℝ) (hd : 0 < d) (hdu : d ≤ 1/200) :
    c1Factor * d ^ (5/4 : ℝ) < d := by
  have hroot : c1Factor * d ^ (1/4 : ℝ) < 1 := by
    apply lt_of_pow_lt_pow_left₀ 4 (by norm_num : (0 : ℝ) ≤ 1)
    rw [mul_pow, c1Factor_pow_four, quarter_pow_four d hd.le]
    norm_num
    linarith
  rw [fiveFourths_eq_mul_quarter d hd]
  nlinarith [mul_lt_mul_of_pos_left hroot hd]

/-- The middle first-cone interval, including both endpoints. -/
theorem c1_middle (d : ℝ) (hdl : 1/200 ≤ d) (hdu : d ≤ 9/1000) :
    c1Factor * d ^ (5/4 : ℝ) < (4/3)*d-7/4000 := by
  change c1Factor * d ^ (5/4 : ℝ) < (4/3)*d + -(7/4000)
  apply affine_dominates_fiveFourths_closed c1Factor (4/3) (-(7/4000)) (1/200) (9/1000) d
    c1Factor_pos.le (by norm_num) (by norm_num) hdl hdu
  · apply endpoint_of_fourth_powers
    · norm_num
    · norm_num
    · rw [c1Factor_pow_four]; norm_num
  · apply endpoint_of_fourth_powers
    · norm_num
    · norm_num
    · rw [c1Factor_pow_four]; norm_num

/-- The upper first-cone interval, including the determinant upper bound. -/
theorem c1_high (d : ℝ) (hdl : 9/1000 ≤ d) (hdu : d ≤ 1/80) :
    c1Factor * d ^ (5/4 : ℝ) < (3/2)*d-33/10000 := by
  change c1Factor * d ^ (5/4 : ℝ) < (3/2)*d + -(33/10000)
  apply affine_dominates_fiveFourths_closed c1Factor (3/2) (-(33/10000)) (9/1000) (1/80) d
    c1Factor_pos.le (by norm_num) (by norm_num) hdl hdu
  · apply endpoint_of_fourth_powers
    · norm_num
    · norm_num
    · rw [c1Factor_pow_four]; norm_num
  · apply endpoint_of_fourth_powers
    · norm_num
    · norm_num
    · rw [c1Factor_pow_four]; norm_num

/-- The first-cone scalar bound is strict everywhere on its determinant range. -/
theorem c1_strict (d : ℝ) (hd : 0 < d) (hdu : d ≤ 1/80) :
    c1Factor * d ^ (5/4 : ℝ) < max d (max ((4/3)*d-7/4000) ((3/2)*d-33/10000)) := by
  by_cases hlow : d ≤ 1/200
  · exact (c1_low d hd hlow).trans_le (le_max_left _ _)
  · by_cases hmid : d ≤ 9/1000
    · exact (c1_middle d (le_of_not_ge hlow) hmid).trans_le
        ((le_max_left _ _).trans (le_max_right _ _))
    · exact (c1_high d (le_of_not_ge hmid) hdu).trans_le
        ((le_max_right _ _).trans (le_max_right _ _))

/-- Applying the scalar result to any normalized numerator satisfying the three bounds. -/
theorem c23_of_three_bounds (d n : ℝ) (hd : 0 < d) (hdu : d ≤ 1)
    (h₁ : 80*d ≤ n) (h₂ : (328/3)*d-41/4 ≤ n) (h₃ : 124*d-20 ≤ n) :
    104 * d ^ (5/4 : ℝ) ≤ n :=
  (c23_bound d hd hdu).trans (max_le h₁ (max_le h₂ h₃))

/-- Equality in any such numerator bound forces the maximal normalized determinant. -/
theorem c23_numerator_equality_forces_one (d n : ℝ) (hd : 0 < d) (hdu : d ≤ 1)
    (h₁ : 80*d ≤ n) (h₂ : (328/3)*d-41/4 ≤ n) (h₃ : 124*d-20 ≤ n)
    (heq : n = 104 * d ^ (5/4 : ℝ)) : d = 1 := by
  by_contra hne
  have h := (c23_strict d hd (lt_of_le_of_ne hdu hne)).trans_le
    (max_le h₁ (max_le h₂ h₃))
  rw [heq] at h
  exact (lt_irrefl _) h

/-- Applying the first-cone scalar result to a normalized numerator. -/
theorem c1_of_three_bounds (d s : ℝ) (hd : 0 < d) (hdu : d ≤ 1/80)
    (h₁ : d ≤ s) (h₂ : (4/3)*d-7/4000 ≤ s) (h₃ : (3/2)*d-33/10000 ≤ s) :
    c1Factor * d ^ (5/4 : ℝ) < s :=
  (c1_strict d hd hdu).trans_le (max_le h₁ (max_le h₂ h₃))

/-- The normalized first-cone moment has strictly larger quantization constant.
The hypotheses here are precisely the three scalar numerator bounds and
normalized determinant bound; the geometric derivation of those hypotheses
is separate from this theorem. -/
theorem c1_quantization_of_three_bounds (d s : ℝ) (hd : 0 < d) (hdu : d ≤ 1/80)
    (h₁ : d ≤ s) (h₂ : (4/3)*d-7/4000 ≤ s) (h₃ : (3/2)*d-33/10000 ≤ s) :
    13 / (120 * Real.sqrt 2) < s / (48 * d ^ (5/4 : ℝ)) := by
  apply (lt_div_iff₀ (mul_pos (by norm_num) (Real.rpow_pos_of_pos hd _))).2
  have h := c1_of_three_bounds d s hd hdu h₁ h₂ h₃
  rw [c1Factor_eq_target] at h
  nlinarith only [h]

/-- Homogeneity of the five-fourths power under a fourth-power scaling. -/
theorem fourth_power_fiveFourths (t : ℝ) (ht : 0 ≤ t) :
    (t ^ (4 : ℕ)) ^ (5/4 : ℝ) = t ^ (5 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num
  exact Real.rpow_natCast t 5

private theorem four_fiveFourths : (4 : ℝ) ^ (5/4 : ℝ) = 4 * Real.sqrt 2 := by
  apply (pow_left_inj₀ (Real.rpow_nonneg (by norm_num) _) (by positivity)
    (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [fiveFourths_pow_four 4 (by norm_num)]
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  calc
    (4 : ℝ)^5 = 4^4 * (2:ℝ)^2 := by norm_num
    _ = 4^4 * ((Real.sqrt 2)^2)^2 := by rw [hs]
    _ = (4 * Real.sqrt 2)^4 := by ring

/-- Exact rescaling of the second/third-cone comparison. -/
theorem c23_scaled_power (D t : ℝ) (hD : 0 ≤ D) (ht : 0 < t) :
    (104 * (D / (4*t^4)) ^ (5/4 : ℝ)) * t^5 =
      13 * Real.sqrt 2 * D ^ (5/4 : ℝ) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hc : (104 : ℝ)/(4*Real.sqrt 2)=13*Real.sqrt 2 := by
    field_simp
    nlinarith only [hs]
  rw [Real.div_rpow hD (by positivity), Real.mul_rpow (by norm_num) (by positivity),
    four_fiveFourths, fourth_power_fiveFourths t ht.le]
  calc
    _ = (104 / (4*Real.sqrt 2)) * D ^ (5/4 : ℝ) := by field_simp; ring
    _ = _ := by rw [hc]

/-- Exact rescaling of the first-cone comparison. -/
theorem c1_scaled_power (D L : ℝ) (hD : 0 ≤ D) (hL : 0 < L) :
    (c1Factor * (D / L^4) ^ (5/4 : ℝ)) * L^5 =
      c1Factor * D ^ (5/4 : ℝ) := by
  rw [Real.div_rpow hD (by positivity), fourth_power_fiveFourths L hL.le]
  field_simp

/-- The second/third-cone polynomial comparison, conditional on the stated
moment bounds and determinant estimate. These are explicit hypotheses;
this theorem does not assume or claim a lattice classification. -/
theorem c23_homogeneous_bound (D t N : ℝ) (hD : 0 < D) (ht : 0 < t)
    (hdet : D ≤ 4*t^4)
    (h₁ : 20*D*t ≤ N)
    (h₂ : (82/3)*D*t-(41/4)*t^5 ≤ N)
    (h₃ : 31*D*t-20*t^5 ≤ N) :
    13 * Real.sqrt 2 * D ^ (5/4 : ℝ) ≤ N := by
  let d := D/(4*t^4)
  have hp : 0 < t^5 := pow_pos ht 5
  have hd : 0 < d := div_pos hD (by positivity)
  have hdu : d ≤ 1 := (div_le_one (by positivity)).2 hdet
  have hn₁ : 80*d ≤ N/t^5 := by
    apply (le_div_iff₀ hp).2
    have hi : 80*d*t^5 = 20*D*t := by dsimp [d]; field_simp; ring
    rwa [hi]
  have hn₂ : (328/3)*d-41/4 ≤ N/t^5 := by
    apply (le_div_iff₀ hp).2
    have hi : ((328/3)*d-41/4)*t^5 = (82/3)*D*t-(41/4)*t^5 := by
      dsimp [d]; field_simp; ring
    rwa [hi]
  have hn₃ : 124*d-20 ≤ N/t^5 := by
    apply (le_div_iff₀ hp).2
    have hi : (124*d-20)*t^5 = 31*D*t-20*t^5 := by dsimp [d]; field_simp; ring
    rwa [hi]
  have h := (le_div_iff₀ hp).1 (c23_of_three_bounds d (N/t^5) hd hdu hn₁ hn₂ hn₃)
  rwa [c23_scaled_power D t hD.le ht] at h

/-- The homogeneous second/third-cone comparison is strict unless the
arithmetic-geometric-mean determinant bound is attained. -/
theorem c23_homogeneous_strict (D t N : ℝ) (hD : 0 < D) (ht : 0 < t)
    (hdet : D < 4*t^4)
    (h₁ : 20*D*t ≤ N)
    (h₂ : (82/3)*D*t-(41/4)*t^5 ≤ N)
    (h₃ : 31*D*t-20*t^5 ≤ N) :
    13 * Real.sqrt 2 * D ^ (5/4 : ℝ) < N := by
  let d := D/(4*t^4)
  have hp : 0 < t^5 := pow_pos ht 5
  have hd : 0 < d := div_pos hD (by positivity)
  have hdu : d < 1 := (div_lt_one (by positivity)).2 hdet
  have hn₁ : 80*d ≤ N/t^5 := by
    apply (le_div_iff₀ hp).2
    have hi : 80*d*t^5 = 20*D*t := by dsimp [d]; field_simp; ring
    rwa [hi]
  have hn₂ : (328/3)*d-41/4 ≤ N/t^5 := by
    apply (le_div_iff₀ hp).2
    have hi : ((328/3)*d-41/4)*t^5 = (82/3)*D*t-(41/4)*t^5 := by
      dsimp [d]; field_simp; ring
    rwa [hi]
  have hn₃ : 124*d-20 ≤ N/t^5 := by
    apply (le_div_iff₀ hp).2
    have hi : (124*d-20)*t^5 = 31*D*t-20*t^5 := by dsimp [d]; field_simp; ring
    rwa [hi]
  have h := (lt_div_iff₀ hp).1 ((c23_strict d hd hdu).trans_le
    (max_le hn₁ (max_le hn₂ hn₃)))
  rwa [c23_scaled_power D t hD.le ht] at h

/-- Equality in the homogeneous second/third-cone bound forces equality
in its determinant estimate. -/
theorem c23_homogeneous_equality_forces_det (D t N : ℝ) (hD : 0 < D) (ht : 0 < t)
    (hdet : D ≤ 4*t^4)
    (h₁ : 20*D*t ≤ N)
    (h₂ : (82/3)*D*t-(41/4)*t^5 ≤ N)
    (h₃ : 31*D*t-20*t^5 ≤ N)
    (heq : N = 13 * Real.sqrt 2 * D ^ (5/4 : ℝ)) : D = 4*t^4 := by
  by_contra hne
  have h := c23_homogeneous_strict D t N hD ht (lt_of_le_of_ne hdet hne) h₁ h₂ h₃
  rw [heq] at h
  exact (lt_irrefl _) h

/-- The homogeneous first-cone comparison, conditional on its three
moment bounds and its determinant estimate, is always strict. -/
theorem c1_homogeneous_strict (D L S : ℝ) (hD : 0 < D) (hL : 0 < L)
    (hdet : D ≤ L^4/80)
    (h₁ : D*L ≤ S)
    (h₂ : (4/3)*D*L-(7/4000)*L^5 ≤ S)
    (h₃ : (3/2)*D*L-(33/10000)*L^5 ≤ S) :
    c1Factor * D ^ (5/4 : ℝ) < S := by
  let d := D/L^4
  have hp : 0 < L^5 := pow_pos hL 5
  have hd : 0 < d := div_pos hD (by positivity)
  have hdu : d ≤ 1/80 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < L^4)).2
    linarith only [hdet]
  have hn₁ : d ≤ S/L^5 := by
    apply (le_div_iff₀ hp).2
    have hi : d*L^5 = D*L := by dsimp [d]; field_simp; ring
    rwa [hi]
  have hn₂ : (4/3)*d-7/4000 ≤ S/L^5 := by
    apply (le_div_iff₀ hp).2
    have hi : ((4/3)*d-7/4000)*L^5 = (4/3)*D*L-(7/4000)*L^5 := by
      dsimp [d]; field_simp; ring
    rwa [hi]
  have hn₃ : (3/2)*d-33/10000 ≤ S/L^5 := by
    apply (le_div_iff₀ hp).2
    have hi : ((3/2)*d-33/10000)*L^5 = (3/2)*D*L-(33/10000)*L^5 := by
      dsimp [d]; field_simp; ring
    rwa [hi]
  have h := (lt_div_iff₀ hp).1 (c1_of_three_bounds d (S/L^5) hd hdu hn₁ hn₂ hn₃)
  rwa [c1_scaled_power D L hD.le hL] at h

end D4
