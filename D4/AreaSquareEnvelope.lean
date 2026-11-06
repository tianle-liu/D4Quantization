import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! The actual square-envelope integral in Lemma d4-area-integral. -/
noncomputable section
namespace D4.AreaEnvelope
open MeasureTheory Set

theorem integral_min_affine (R a b : ℝ) (hleft : -R ≤ a-b) (hright : a-b ≤ R) :
    (∫ y in -R..R, min a (y+b)) =
      R*(a+b) - (a-b)^2/2 - R^2/2 := by
  have hc : Continuous (fun y : ℝ => min a (y+b)) := by fun_prop
  have hl : (∫ y in -R..(a-b), min a (y+b)) = ∫ y in -R..(a-b), y+b := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hleft] at hy
    exact min_eq_right (by linarith [hy.2])
  have hr : (∫ y in (a-b)..R, min a (y+b)) = ∫ y in (a-b)..R, a := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hright] at hy
    exact min_eq_left (by linarith [hy.1])
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-R) (a-b)) (hc.intervalIntegrable (a-b) R),hl,hr,
    intervalIntegral.integral_add (f := fun y : ℝ => y) (g := fun _ : ℝ => b)
      (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,integral_id,intervalIntegral.integral_const,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

def squareEnvelope (R δ : ℝ) : ℝ :=
  ∫ x in -R..R, ∫ y in -R..R, min (min 0 x) (min y (x+y+δ))

def squareSlice (R δ x : ℝ) : ℝ :=
  R*(min 0 x + min 0 (x+δ)) - (min 0 x - min 0 (x+δ))^2/2 - R^2/2

theorem squareEnvelope_eq_slices (R δ : ℝ) (hδ : |δ| ≤ R) :
    squareEnvelope R δ = ∫ x in -R..R, squareSlice R δ x := by
  unfold squareEnvelope
  apply intervalIntegral.integral_congr
  intro x _
  have he : (fun y : ℝ => min (min 0 x) (min y (x+y+δ))) =
      fun y => min (min 0 x) (y+min 0 (x+δ)) := by
    funext y
    congr 1
    rw [add_min]
    congr 1 <;> ring
  dsimp only
  rw [he]
  apply integral_min_affine
  · have hmin : min 0 x - min 0 (x+δ) ≥ -|δ| := by
      rcases le_total x 0 with hx | hx <;> rcases le_total (x+δ) 0 with hxd | hxd
      all_goals simp only [min_eq_right hx, min_eq_left hx, min_eq_right hxd, min_eq_left hxd]
      all_goals linarith [le_abs_self δ, neg_abs_le δ]
    linarith
  · have hmin : min 0 x - min 0 (x+δ) ≤ |δ| := by
      rcases le_total x 0 with hx | hx <;> rcases le_total (x+δ) 0 with hxd | hxd
      all_goals simp only [min_eq_right hx, min_eq_left hx, min_eq_right hxd, min_eq_left hxd]
      all_goals linarith [le_abs_self δ, neg_abs_le δ]
    linarith

theorem integral_poly2 (a b c l u : ℝ) :
    (∫ x in l..u, a*x^2+b*x+c) =
      a*(u^3-l^3)/3+b*(u^2-l^2)/2+c*(u-l) := by
  have ha : IntervalIntegrable (fun x : ℝ => a*x^2) volume l u :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  have hb : IntervalIntegrable (fun x : ℝ => b*x) volume l u :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (ha.add hb) intervalIntegrable_const,
    intervalIntegral.integral_add ha hb, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,integral_pow,integral_id,intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem squareEnvelope_nonneg (R δ : ℝ) (hδ : 0 ≤ δ) (hR : δ ≤ R) :
    squareEnvelope R δ = -2*R^3+R^2*δ-R*δ^2+δ^3/3 := by
  rw [squareEnvelope_eq_slices R δ (by simpa [abs_of_nonneg hδ] using hR)]
  have hc : Continuous (squareSlice R δ) := by unfold squareSlice; fun_prop
  have h1 : (∫ x in -R..(-δ), squareSlice R δ x) =
      ∫ x in -R..(-δ), 0*x^2+(2*R)*x+(R*δ-δ^2/2-R^2/2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : -R ≤ -δ)] at hx
    have hx0 : x ≤ 0 := by linarith [hx.2]
    have hxd : x+δ ≤ 0 := by linarith [hx.2]
    simp only [squareSlice, min_eq_right hx0, min_eq_right hxd]
    ring
  have h2 : (∫ x in (-δ)..0, squareSlice R δ x) =
      ∫ x in (-δ)..0, (-1/2:ℝ)*x^2+R*x+(-R^2/2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : -δ ≤ 0)] at hx
    have hxd : 0 ≤ x+δ := by linarith [hx.1]
    simp only [squareSlice, min_eq_right hx.2, min_eq_left hxd]
    ring
  have h3 : (∫ x in (0:ℝ)..R, squareSlice R δ x) =
      ∫ x in (0:ℝ)..R, 0*x^2+0*x+(-R^2/2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (hδ.trans hR)] at hx
    have hxd : 0 ≤ x+δ := by linarith [hx.1]
    simp only [squareSlice, min_eq_left hx.1, min_eq_left hxd]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-R) (-δ))
      (hc.intervalIntegrable (-δ) R),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-δ) 0)
      (hc.intervalIntegrable 0 R),h1,h2,h3,integral_poly2,integral_poly2,integral_poly2]
  ring

theorem squareEnvelope_nonpos (R δ : ℝ) (hδ : δ ≤ 0) (hR : -δ ≤ R) :
    squareEnvelope R δ = -2*R^3+R^2*δ-R*δ^2+δ^3/6 := by
  rw [squareEnvelope_eq_slices R δ (by simpa [abs_of_nonpos hδ] using hR)]
  have hc : Continuous (squareSlice R δ) := by unfold squareSlice; fun_prop
  have hR0 : 0 ≤ R := by linarith
  have h1 : (∫ x in -R..0, squareSlice R δ x) =
      ∫ x in -R..0, 0*x^2+(2*R)*x+(R*δ-δ^2/2-R^2/2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : -R ≤ 0)] at hx
    have hxd : x+δ ≤ 0 := by linarith [hx.2]
    simp only [squareSlice, min_eq_right hx.2, min_eq_right hxd]
    ring
  have h2 : (∫ x in (0:ℝ)..(-δ), squareSlice R δ x) =
      ∫ x in (0:ℝ)..(-δ), (-1/2:ℝ)*x^2+(R-δ)*x+(R*δ-δ^2/2-R^2/2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : 0 ≤ -δ)] at hx
    have hxd : x+δ ≤ 0 := by linarith [hx.2]
    simp only [squareSlice, min_eq_left hx.1, min_eq_right hxd]
    ring
  have h3 : (∫ x in (-δ)..R, squareSlice R δ x) =
      ∫ x in (-δ)..R, 0*x^2+0*x+(-R^2/2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hR] at hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hxd : 0 ≤ x+δ := by linarith [hx.1]
    simp only [squareSlice, min_eq_left hx0, min_eq_left hxd]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-R) 0)
      (hc.intervalIntegrable 0 R),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (-δ))
      (hc.intervalIntegrable (-δ) R),h1,h2,h3,integral_poly2,integral_poly2,integral_poly2]
  ring

/-- The polynomial continuation from the negative side. -/
def squareNegativePolynomial (R δ : ℝ) : ℝ := -2*R^3+R^2*δ-R*δ^2+δ^3/6

theorem squareEnvelope_positivePart (R δ : ℝ) (hδ : |δ| ≤ R) :
    squareEnvelope R δ - squareNegativePolynomial R δ = (max δ 0)^3/6 := by
  rcases le_total δ 0 with hd | hd
  · rw [squareEnvelope_nonpos R δ hd (by simpa [abs_of_nonpos hd] using hδ), max_eq_right hd]
    unfold squareNegativePolynomial
    ring
  · rw [squareEnvelope_nonneg R δ hd (by simpa [abs_of_nonneg hd] using hδ), max_eq_left hd]
    unfold squareNegativePolynomial
    ring

/-- The nested interval integral is exactly Lebesgue integration on the square. -/
theorem squareEnvelope_eq_squareIntegral (R δ : ℝ) (hR : 0 ≤ R) :
    squareEnvelope R δ =
      ∫ p in Icc (-R) R ×ˢ Icc (-R) R,
        min (min 0 p.1) (min p.2 (p.1+p.2+δ)) := by
  have hc : Continuous (fun p : ℝ × ℝ => min (min 0 p.1) (min p.2 (p.1+p.2+δ))) := by fun_prop
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod _ (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))]
  unfold squareEnvelope
  rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R), ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  dsimp only
  rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R), ← integral_Icc_eq_integral_Ioc]

end D4.AreaEnvelope
