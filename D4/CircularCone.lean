import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# The derivative calculation for circular cones

This is the actual real derivative in equation (cone-derivative), expressed
using negative powers. The pyramid comparison and Theorem B combine it
with the geometric integrations and change of angle proved in later modules.
-/
noncomputable section
namespace D4.CircularCone

def alpha (d : ℝ) : ℝ := (d - 1) / (d + 1)

def slope (d s : ℝ) : ℝ :=
  (d - 1 - alpha d * s) * (1 + s) ^ (d / 2) *
    (1 + alpha d * s) ^ (-d / 2 - 1)

def slopeDerivative (d s : ℝ) : ℝ :=
  -(d * (d - 1) * (d + 2) / (d + 1)^2) * s *
    (1 + s) ^ (d / 2 - 1) * (1 + alpha d * s) ^ (-d / 2 - 2)

theorem alpha_pos (d : ℝ) (hd : 2 ≤ d) : 0 < alpha d := by
  unfold alpha
  exact div_pos (by linarith) (by linarith)

theorem numerator_identity (d s : ℝ) (hd : d + 1 ≠ 0) :
    -alpha d * (1+s) * (1+alpha d*s) +
      (d-1-alpha d*s) * (d/2) * (1+alpha d*s) +
      (d-1-alpha d*s) * alpha d * (-d/2-1) * (1+s) =
    -(d*(d-1)*(d+2)/(d+1)^2)*s := by
  unfold alpha
  field_simp
  ring

theorem hasDerivAt_slope (d s : ℝ) (hd : 2 ≤ d) (hs : 0 < s) :
    HasDerivAt (slope d) (slopeDerivative d s) s := by
  have ha := alpha_pos d hd
  have hx : 0 < 1+s := by linarith
  have hy : 0 < 1+alpha d*s := by positivity
  have hlin := ((hasDerivAt_id s).const_mul (alpha d)).const_sub (d-1)
  have hbase := (hasDerivAt_id s).const_add 1
  have hp := hbase.rpow_const (p := d/2) (Or.inl hx.ne')
  have hbase2 := ((hasDerivAt_id s).const_mul (alpha d)).const_add 1
  have hq := hbase2.rpow_const (p := -d/2-1) (Or.inl hy.ne')
  have hall := (hlin.mul hp).mul hq
  have hxp : (1+s)^(d/2) = (1+s)^(d/2-1)*(1+s) := by
    rw [← Real.rpow_add_one hx.ne']
    congr 1
    ring
  have hyp : (1+alpha d*s)^(-d/2-1) =
      (1+alpha d*s)^(-d/2-2)*(1+alpha d*s) := by
    rw [← Real.rpow_add_one hy.ne']
    congr 1
    ring
  convert hall using 1
  dsimp [slopeDerivative]
  simp only [mul_one, one_mul, id_eq] at *
  rw [hxp, hyp]
  have hn := numerator_identity d s (by linarith)
  have hexp : -d/2-1-1 = -d/2-2 := by ring
  rw [hexp]
  have hn' := congrArg
    (fun z : ℝ => z * (1+s)^(d/2-1) * (1+alpha d*s)^(-d/2-2)) hn
  linear_combination -hn'

theorem slopeDerivative_neg (d s : ℝ) (hd : 2 ≤ d) (hs : 0 < s) :
    slopeDerivative d s < 0 := by
  have ha := alpha_pos d hd
  have hx : 0 < 1+s := by linarith
  have hy : 0 < 1+alpha d*s := by positivity
  unfold slopeDerivative
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos
    · apply mul_neg_of_neg_of_pos
      · apply neg_neg_of_pos
        apply div_pos
        · have : 0 < d := by linarith
          have : 0 < d-1 := by linarith
          have : 0 < d+2 := by linarith
          positivity
        · positivity
      · exact hs
    · exact Real.rpow_pos_of_pos hx _
  · exact Real.rpow_pos_of_pos hy _

theorem slope_eq_quotient (d s : ℝ) (hd : 2 ≤ d) (hs : 0 < s) :
    slope d s = ((d-1)-alpha d*s) * (1+s)^(d/2) /
      (1+alpha d*s)^(d/2+1) := by
  have ha := alpha_pos d hd
  have hy : 0 < 1+alpha d*s := by positivity
  unfold slope
  rw [show -d/2-1 = -(d/2+1) by ring, Real.rpow_neg hy.le]
  rfl

theorem slope_strictAntiOn (d : ℝ) (hd : 2 ≤ d) :
    StrictAntiOn (slope d) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
  · intro s hs
    exact (hasDerivAt_slope d s hd hs).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : 0 < s := (interior_subset hs : s ∈ Set.Ioi (0 : ℝ))
    rw [(hasDerivAt_slope d s hd hs').deriv]
    exact slopeDerivative_neg d s hd hs'

end D4.CircularCone
