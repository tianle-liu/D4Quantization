import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cubic Schur inequality

This elementary inequality is the only non-monomial nonnegative factor in
some of the paper's exact certificates. Its proof is a polynomial identity
and six order cases; it introduces no assumptions beyond nonnegative inputs.
-/
namespace D4

private theorem schur_sorted (x y z : ℝ) (hz : 0 ≤ z)
    (hzy : z ≤ y) (hyx : y ≤ x) :
    0 ≤ x^3+y^3+z^3+3*x*y*z-x^2*y-x^2*z-y^2*x-y^2*z-z^2*x-z^2*y := by
  have h₁ : 0 ≤ (x-y)^2 * (x+y-z) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have h₂ : 0 ≤ z * (x-z) * (y-z) :=
    mul_nonneg (mul_nonneg hz (by linarith)) (sub_nonneg.mpr hzy)
  nlinarith only [h₁, h₂]

/-- Schur's cubic inequality for nonnegative real inputs. -/
theorem schur_nonneg (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 ≤ u^3+v^3+w^3+3*u*v*w-u^2*v-u^2*w-v^2*u-v^2*w-w^2*u-w^2*v := by
  rcases le_total u v with huv | hvu
  · rcases le_total v w with hvw | hwv
    · nlinarith only [schur_sorted w v u hu huv hvw]
    · rcases le_total u w with huw | hwu
      · nlinarith only [schur_sorted v w u hu huw hwv]
      · nlinarith only [schur_sorted v u w hw hwu huv]
  · rcases le_total u w with huw | hwu
    · nlinarith only [schur_sorted w u v hv hvu huw]
    · rcases le_total v w with hvw | hwv
      · nlinarith only [schur_sorted u w v hv hvw hwu]
      · nlinarith only [schur_sorted u v w hw hwv hvu]

end D4
