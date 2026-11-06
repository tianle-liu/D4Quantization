import D4.PrincipalBoundary

/-! Positive approximation extends each genuine secondary-cone moment
formula to all of its positive-definite nonnegative boundary. -/
noncomputable section
open Matrix Set Filter
open scoped Topology
namespace D4.Principal
open Analytic

theorem secondary_isHermitian (g : Fin 9 → Vec) (a : ℝ) (w : Fin 9 → ℝ) :
    (secondaryForm g a w).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hA : gramMatrix ℝ j i = gramMatrix ℝ i j := by
    simpa only [star_trivial] using gramMatrix_posDef.isHermitian.apply i j
  simp only [secondaryForm, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, rankOne, star_trivial]
  rw [hA]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem quadratic_secondary (g : Fin 9 → Vec) (a : ℝ) (w : Fin 9 → ℝ) (x : Vec) :
    quadratic (secondaryForm g a w) x =
      a * quadratic (gramMatrix ℝ) x + ∑ i, w i * dotProduct x (g i)^2 := by
  have hadd (A B : Gram) : quadratic (A + B) x = quadratic A x + quadratic B x := by
    simp only [quadratic, Matrix.add_mulVec, dotProduct_add]
  rw [secondaryForm, hadd, quadratic_smul, quadratic_sum]
  simp only [quadratic_smul, quadratic_rankOne]

theorem secondary_posDef_of_pos (g : Fin 9 → Vec) {a : ℝ} (ha : 0 < a)
    {w : Fin 9 → ℝ} (hw : ∀ i, 0 ≤ w i) : (secondaryForm g a w).PosDef := by
  refine ⟨secondary_isHermitian g a w, ?_⟩
  intro x hx
  have hA : 0 < quadratic (gramMatrix ℝ) x := by
    simpa only [quadratic, star_trivial] using gramMatrix_posDef.2 x hx
  have hs : 0 ≤ ∑ i, w i * dotProduct x (g i)^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have h : 0 < quadratic (secondaryForm g a w) x := by
    rw [quadratic_secondary]
    exact add_pos_of_pos_of_nonneg (mul_pos ha hA) hs
  simpa only [quadratic, star_trivial] using h

theorem secondaryForm_continuous (g : Fin 9 → Vec) :
    Continuous (fun w : Fin 10 → ℝ => secondaryForm g (w 0) (fun j => w j.succ)) := by
  unfold secondaryForm
  fun_prop

theorem secondary_moment_boundary_extension (g : Fin 9 → Vec)
    (F : (Fin 10 → ℝ) → ℝ) (hF : Continuous F)
    (hpositive : ∀ w : Fin 10 → ℝ, (∀ e, 0 < w e) →
      12 * (secondaryForm g (w 0) (fun j => w j.succ)).det *
        moment (secondaryForm g (w 0) (fun j => w j.succ)) = F w)
    {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e)
    (hQ : (secondaryForm g (w 0) (fun j => w j.succ)).PosDef) :
    12 * (secondaryForm g (w 0) (fun j => w j.succ)).det *
      moment (secondaryForm g (w 0) (fun j => w j.succ)) = F w := by
  have hwlim := positiveApprox_tendsto w
  have hQlim := (secondaryForm_continuous g).continuousAt.tendsto.comp hwlim
  have hMlim := moment_tendsto hQ hQlim (Eventually.of_forall fun n =>
    secondary_posDef_of_pos g (positiveApprox_pos hw n 0)
      (fun j => (positiveApprox_pos hw n j.succ).le))
  have hdetlim := continuous_id.matrix_det.continuousAt.tendsto.comp hQlim
  have hl := ((tendsto_const_nhds (x := (12 : ℝ))).mul hdetlim).mul hMlim
  have hr := hF.continuousAt.tendsto.comp hwlim
  apply tendsto_nhds_unique hl
  apply hr.congr'
  exact Eventually.of_forall (fun n => (hpositive _ (positiveApprox_pos hw n)).symm)

end D4.Principal
