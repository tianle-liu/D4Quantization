import D4.NearestPoint
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix

/-!
# Continuity of the genuine lattice moment on positive-definite forms

The proof uses quadratic coercivity and relative comparison of quadratic
forms. It applies to the actual infinite nearest-point infimum and Lebesgue
integral. No cone-specific moment polynomial, Voronoi classification, or
assumed continuity statement enters the proof.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Topology
namespace D4.Analytic

-- Choose the entrywise supremum norm; all continuity claims use the usual
-- finite-product topology on matrices.
attribute [local instance] Matrix.normedAddCommGroup

private theorem quadratic_eq_sum (Q : Gram) (x : Vec) :
    quadratic Q x = ∑ i : Fin 4, ∑ j : Fin 4, x i * Q i j * x j := by
  simp [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- An entrywise norm estimate, valid for every matrix, not just symmetric ones. -/
theorem abs_quadratic_le (Q : Gram) (x : Vec) :
    |quadratic Q x| ≤ 16 * ‖Q‖ * ‖x‖^2 := by
  rw [quadratic_eq_sum]
  calc
    |∑ i : Fin 4, ∑ j : Fin 4, x i * Q i j * x j| ≤
        ∑ i : Fin 4, ∑ j : Fin 4, |x i * Q i j * x j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, ‖x‖ * ‖Q‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hi : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
      have hj : |x j| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
      have hq : |Q i j| ≤ ‖Q‖ := by
        simpa [Real.norm_eq_abs] using (norm_le_pi_norm (Q i) j).trans (norm_le_pi_norm Q i)
      simp only [abs_mul]
      exact mul_le_mul (mul_le_mul hi hq (abs_nonneg _) (norm_nonneg _)) hj
        (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = 16 * ‖Q‖ * ‖x‖^2 := by simp; ring

theorem quadratic_sub_matrix (Q R : Gram) (x : Vec) :
    quadratic (R-Q) x = quadratic R x - quadratic Q x := by
  simp [quadratic, Matrix.sub_mulVec, dotProduct_sub]

/-- Coercivity turns a matrix perturbation into a relative quadratic-form bound. -/
theorem quadratic_relative_difference (Q R : Gram) {c : ℝ} (hc : 0 < c)
    (hcoerce : ∀ y : Vec, c * ‖y‖^2 ≤ quadratic Q y) (y : Vec) :
    |quadratic R y - quadratic Q y| ≤ (16 * ‖R-Q‖ / c) * quadratic Q y := by
  rw [← quadratic_sub_matrix]
  have hscale := mul_le_mul_of_nonneg_left (hcoerce y)
    (div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) (norm_nonneg (R-Q))) hc.le)
  calc
    |quadratic (R-Q) y| ≤ 16 * ‖R-Q‖ * ‖y‖^2 := abs_quadratic_le _ _
    _ ≤ (16 * ‖R-Q‖ / c) * quadratic Q y := by
      convert hscale using 1
      field_simp
      ring

/-- Relative form comparison also bounds the actual infinite nearest-point infimum. -/
theorem nearest_relative_difference {Q R : Gram} (hQ : Q.PosDef) (hR : R.PosDef)
    {c : ℝ} (hc : 0 < c) (hcoerce : ∀ y : Vec, c * ‖y‖^2 ≤ quadratic Q y)
    (hclose : 16 * ‖R-Q‖ / c ≤ 1) (x : Vec) :
    |nearest R x - nearest Q x| ≤ (16 * ‖R-Q‖ / c) * nearest Q x := by
  let e := 16 * ‖R-Q‖ / c
  have hdiff (y : Vec) := abs_le.mp (quadratic_relative_difference Q R hc hcoerce y)
  obtain ⟨z, hz⟩ := nearest_attained hQ x
  have hu : nearest R x ≤ (1+e) * nearest Q x := by
    have hn := nearest_le hR.posSemidef x z
    have hh := (hdiff (x - castVec z)).2
    rw [← hz] at hh
    dsimp [e]
    linarith only [hn, hh]
  have hl : (1-e) * nearest Q x ≤ nearest R x := by
    apply le_ciInf
    intro w
    have hn := mul_le_mul_of_nonneg_left (nearest_le hQ.posSemidef x w)
      (sub_nonneg.mpr hclose)
    have hh := (hdiff (x - castVec w)).1
    dsimp [e]
    nlinarith only [hn, hh]
  apply abs_le.mpr
  constructor <;> dsimp [e] at * <;> nlinarith only [hu, hl]

/-- The same relative estimate holds after integration over the fundamental cube. -/
theorem moment_relative_difference {Q R : Gram} (hQ : Q.PosDef) (hR : R.PosDef)
    {c : ℝ} (hc : 0 < c) (hcoerce : ∀ y : Vec, c * ‖y‖^2 ≤ quadratic Q y)
    (hclose : 16 * ‖R-Q‖ / c ≤ 1) :
    |moment R - moment Q| ≤ (16 * ‖R-Q‖ / c) * moment Q := by
  let e := 16 * ‖R-Q‖ / c
  have hl (x : Vec) : (1-e)*nearest Q x ≤ nearest R x := by
    have h := (abs_le.mp (nearest_relative_difference hQ hR hc hcoerce hclose x)).1
    dsimp [e]
    nlinarith only [h]
  have hu (x : Vec) : nearest R x ≤ (1+e)*nearest Q x := by
    have h := (abs_le.mp (nearest_relative_difference hQ hR hc hcoerce hclose x)).2
    dsimp [e]
    nlinarith only [h]
  have hlo := integral_mono (μ := volume.restrict unitCube)
    ((nearest_integrableOn hQ.posSemidef).const_mul (1-e))
    (nearest_integrableOn hR.posSemidef) hl
  have hup := integral_mono (μ := volume.restrict unitCube)
    (nearest_integrableOn hR.posSemidef)
    ((nearest_integrableOn hQ.posSemidef).const_mul (1+e)) hu
  simp only [integral_const_mul] at hlo hup
  change (1-e)*moment Q ≤ moment R at hlo
  change moment R ≤ (1+e)*moment Q at hup
  apply abs_le.mpr
  constructor <;> dsimp [e] at * <;> nlinarith only [hlo, hup]

/-- For each point, nearest-point energy varies continuously with a positive-definite form. -/
theorem nearest_continuousOn_form (x : Vec) :
    ContinuousOn (fun Q : Gram => nearest Q x) {Q | Q.PosDef} := by
  intro Q hQ
  obtain ⟨c, hc, hcoerce⟩ := quadratic_coercive hQ
  let e : Gram → ℝ := fun R => 16 * ‖R-Q‖ / c
  have hecont : Continuous e := by dsimp [e]; fun_prop
  have hezero : e Q = 0 := by simp [e]
  have he : Tendsto e (𝓝[{R : Gram | R.PosDef}] Q) (𝓝 0) := by
    simpa only [hezero] using
      ((hecont.continuousAt (x := Q)).continuousWithinAt
        (s := {R : Gram | R.PosDef})).tendsto
  have hb : Tendsto (fun R => e R * nearest Q x)
      (𝓝[{R : Gram | R.PosDef}] Q) (𝓝 0) := by
    simpa using he.mul_const (nearest Q x)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ hb
  filter_upwards [he (Iio_mem_nhds (by norm_num : (0:ℝ) < 1)), self_mem_nhdsWithin]
    with R hclose hR
  simpa [Real.dist_eq, e] using nearest_relative_difference hQ hR hc hcoerce hclose.le x

/-- Continuity of the true integral on the whole positive-definite cone. -/
theorem moment_continuousOn : ContinuousOn moment {Q : Gram | Q.PosDef} := by
  intro Q hQ
  obtain ⟨c, hc, hcoerce⟩ := quadratic_coercive hQ
  let e : Gram → ℝ := fun R => 16 * ‖R-Q‖ / c
  have hecont : Continuous e := by dsimp [e]; fun_prop
  have hezero : e Q = 0 := by simp [e]
  have he : Tendsto e (𝓝[{R : Gram | R.PosDef}] Q) (𝓝 0) := by
    simpa only [hezero] using
      ((hecont.continuousAt (x := Q)).continuousWithinAt
        (s := {R : Gram | R.PosDef})).tendsto
  have hb : Tendsto (fun R => e R * moment Q)
      (𝓝[{R : Gram | R.PosDef}] Q) (𝓝 0) := by
    simpa using he.mul_const (moment Q)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ hb
  filter_upwards [he (Iio_mem_nhds (by norm_num : (0:ℝ) < 1)), self_mem_nhdsWithin]
    with R hclose hR
  simpa [Real.dist_eq, e] using moment_relative_difference hQ hR hc hcoerce hclose.le

/-- The normalized second moment is continuous on positive-definite forms as well. -/
theorem normalizedMoment_continuousOn :
    ContinuousOn normalizedMoment {Q : Gram | Q.PosDef} := by
  intro Q hQ
  apply (moment_continuousOn Q hQ).div
    (continuousWithinAt_const.mul
      (continuous_id.matrix_det.continuousAt.continuousWithinAt.rpow_const
        (Or.inl hQ.det_pos.ne')))
  exact mul_ne_zero (by norm_num) (Real.rpow_pos_of_pos hQ.det_pos (1/4 : ℝ)).ne'

/-- A form of continuity convenient for approaching a cone boundary.
The limit is required to remain positive definite. -/
theorem moment_tendsto {α : Type*} {l : Filter α} {F : α → Gram} {Q : Gram}
    (hQ : Q.PosDef) (hF : Tendsto F l (𝓝 Q))
    (hpos : ∀ᶠ a in l, (F a).PosDef) :
    Tendsto (fun a => moment (F a)) l (𝓝 (moment Q)) := by
  exact (moment_continuousOn Q hQ).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hF, hpos⟩)

/-- Normalized moments converge along any eventually positive-definite family
converging to a positive-definite form. -/
theorem normalizedMoment_tendsto {α : Type*} {l : Filter α} {F : α → Gram} {Q : Gram}
    (hQ : Q.PosDef) (hF : Tendsto F l (𝓝 Q))
    (hpos : ∀ᶠ a in l, (F a).PosDef) :
    Tendsto (fun a => normalizedMoment (F a)) l (𝓝 (normalizedMoment Q)) := by
  exact (normalizedMoment_continuousOn Q hQ).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hF, hpos⟩)

end D4.Analytic
