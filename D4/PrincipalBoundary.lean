import D4.PrincipalGeometry
import D4.PrincipalVoronoi
import D4.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

/-! Positive principal weights approximate every nonnegative weight vector.
The actual moment identity consequently extends to every positive-definite
boundary point, once proved on the strict cone. -/
noncomputable section
open Matrix Set Filter
open scoped Topology
namespace D4.Principal
open Analytic

def singletonEdge (i : Fin 4) : Fin 10 := ⟨i.val, lt_trans i.isLt (by decide)⟩

theorem singleton_generator_dot (x : Vec) (i : Fin 4) :
    dotProduct x (cone1Vectors (singletonEdge i)) = x i := by
  rw [generator_dot_potential]
  fin_cases i
  · change x 0 - 0 = x 0; ring
  · change x 1 - 0 = x 1; ring
  · change x 2 - 0 = x 2; ring
  · change x 3 - 0 = x 3; ring

theorem principal_posDef_of_pos {w : Fin 10 → ℝ} (hw : ∀ e, 0 < w e) :
    (principalForm w).PosDef := by
  refine ⟨principal_isHermitian w, ?_⟩
  intro x hx
  have hn : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hn
  have hh : 0 < quadratic (principalForm w) x := by
    rw [quadratic_principal]
    apply Finset.sum_pos' (fun e _ => mul_nonneg (hw e).le (sq_nonneg _))
    refine ⟨singletonEdge i, Finset.mem_univ _, ?_⟩
    rw [singleton_generator_dot]
    exact mul_pos (hw _) (sq_pos_of_ne_zero hi)
  simpa only [quadratic, star_trivial] using hh

theorem principalForm_continuous : Continuous principalForm := by
  unfold principalForm
  fun_prop

def positiveApprox (w : Fin 10 → ℝ) (n : ℕ) : Fin 10 → ℝ :=
  fun e => w e + 1 / ((n : ℝ) + 1)

theorem positiveApprox_pos {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e) (n : ℕ) :
    ∀ e, 0 < positiveApprox w n e := by
  intro e
  exact add_pos_of_nonneg_of_pos (hw e) (by positivity)

theorem positiveApprox_tendsto (w : Fin 10 → ℝ) : Tendsto (positiveApprox w) atTop (𝓝 w) := by
  apply tendsto_pi_nhds.mpr
  intro e
  simpa only [positiveApprox, add_zero] using
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat

/-- Extension principle for the actual principal moment numerator. The only
formula premise is its already-proved restriction to strictly positive weights. -/
theorem principal_moment_boundary_extension (F : (Fin 10 → ℝ) → ℝ) (hF : Continuous F)
    (hpositive : ∀ w : Fin 10 → ℝ, (∀ e, 0 < w e) →
      12 * (principalForm w).det * moment (principalForm w) = F w)
    {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e) (hQ : (principalForm w).PosDef) :
    12 * (principalForm w).det * moment (principalForm w) = F w := by
  have hwlim := positiveApprox_tendsto w
  have hQlim := principalForm_continuous.continuousAt.tendsto.comp hwlim
  have hMlim := moment_tendsto hQ hQlim (Eventually.of_forall fun n =>
    principal_posDef_of_pos (positiveApprox_pos hw n))
  have hdetlim := continuous_id.matrix_det.continuousAt.tendsto.comp hQlim
  have hl := ((tendsto_const_nhds (x := (12 : ℝ))).mul hdetlim).mul hMlim
  have hr := hF.continuousAt.tendsto.comp hwlim
  apply tendsto_nhds_unique hl
  apply hr.congr'
  exact Eventually.of_forall (fun n => (hpositive _ (positiveApprox_pos hw n)).symm)

end D4.Principal
