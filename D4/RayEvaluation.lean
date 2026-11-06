import D4.CertificateMomentData
import D4.Targets
import D4.Scalar

/-!
# The supplied moment polynomial on the D₄ ray

Evaluation is checked by integer computation and then transported to the
real polynomial semantics. The actual integral value follows only under
the explicitly stated geometric moment identity.
-/
namespace D4
open Certificate CertificateMoments Matrix

/-- The parameter tuple `a=1`, with all rank-one weights zero. -/
def rayCoordinates (i : Nat) : ℝ := if i = 0 then 1 else 0

theorem rayCoordinates_nonneg (i : Nat) : 0 ≤ rayCoordinates i := by
  unfold rayCoordinates
  split_ifs <;> norm_num

/-- Integer evaluation specialized to the zero/nonzero coordinate test. -/
def evalAtRay (p : Poly) : Int :=
  (p.map fun t => if t.1.all (fun i => i == 0) then t.2 else 0).sum

private theorem monomial_ray (m : Monomial) :
    monomial rayCoordinates m = if m.all (fun i => i == 0) then (1 : ℝ) else 0 := by
  induction m with
  | nil => simp [monomial]
  | cons i m ih =>
    change rayCoordinates i * monomial rayCoordinates m = _
    rw [ih]
    by_cases hi : i = 0 <;> simp [rayCoordinates, hi]

/-- Soundness of the integer ray evaluator for every sparse polynomial. -/
theorem eval_ray_eq (p : Poly) : eval rayCoordinates p = (evalAtRay p : ℝ) := by
  induction p with
  | nil => simp [evalAtRay]
  | cons t ts ih =>
    simp only [eval_cons, monomial_ray, ih, evalAtRay, List.map_cons, List.sum_cons,
      Int.cast_add]
    split_ifs <;> simp

/-- Kernel computation of the exact numerator at the D₄ parameter tuple. -/
theorem momentC2_ray_integer : evalAtRay momentC2 = 104 := by decide +kernel

theorem momentC2_ray_eval : eval rayCoordinates momentC2 = 104 := by
  rw [eval_ray_eq, momentC2_ray_integer]
  norm_num

/-- The parameter tuple maps to the actual matrix A for either secondary cone. -/
theorem ray_secondaryForm (v : Fin 9 → Fin 4 → ℝ) :
    secondaryForm v (rayCoordinates 0) (fun i => rayCoordinates (i+1)) = gramMatrix ℝ := by
  simp [secondaryForm, rayCoordinates]

/-- The true integral at A follows from the stated second-cone moment identity. -/
theorem moment_gramMatrix_of_polynomial_identity
    (hmoment : 60 * (gramMatrix ℝ).det * Analytic.moment (gramMatrix ℝ) =
      eval rayCoordinates momentC2) : Analytic.moment (gramMatrix ℝ) = 13/30 := by
  rw [det_gramMatrix, momentC2_ray_eval] at hmoment
  linarith only [hmoment]

/-- The actual moment value at A gives exactly the claimed quantization constant. -/
theorem normalizedMoment_gramMatrix_of_moment
    (hm : Analytic.moment (gramMatrix ℝ) = 13/30) :
    Analytic.normalizedMoment (gramMatrix ℝ) = Analytic.optimalConstant := by
  have hr : (4 : ℝ) ^ (1/4 : ℝ) = Real.sqrt 2 := by
    apply (pow_left_inj₀ (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
      (by norm_num : (4 : Nat) ≠ 0)).mp
    rw [quarter_pow_four 4 (by norm_num)]
    have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    calc
      (4 : ℝ) = (2 : ℝ)^2 := by norm_num
      _ = ((Real.sqrt 2)^2)^2 := by rw [hs]
      _ = (Real.sqrt 2)^4 := by ring
  unfold Analytic.normalizedMoment Analytic.optimalConstant
  rw [hm, det_gramMatrix, hr]
  ring

end D4
