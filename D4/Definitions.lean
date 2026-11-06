import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The analytic quantity in arXiv:2611.00100v2

These are the actual integral definitions, independent of any polynomial
certificate. No identity between this integral and a moment polynomial is
assumed here. The main lower bound is proved in `D4.CompleteTheoremA`.
-/

noncomputable section
open Matrix MeasureTheory Set

namespace D4.Analytic

abbrev Vec := Fin 4 → ℝ
abbrev IntVec := Fin 4 → ℤ
abbrev Gram := Matrix (Fin 4) (Fin 4) ℝ

def castVec (z : IntVec) : Vec := fun i => (z i : ℝ)

def quadratic (Q : Gram) (x : Vec) : ℝ := dotProduct x (Q *ᵥ x)

/-- Infimum over all integer translates, not over a preselected finite sample. -/
def nearest (Q : Gram) (x : Vec) : ℝ :=
  ⨅ z : IntVec, quadratic Q (x - castVec z)

/-- The cube in the paper, with the product Lebesgue measure on `Fin 4 → ℝ`. -/
def unitCube : Set Vec := Icc 0 1

def moment (Q : Gram) : ℝ := ∫ x in unitCube, nearest Q x

def normalizedMoment (Q : Gram) : ℝ :=
  moment Q / (4 * Q.det ^ (1 / 4 : ℝ))

def optimalConstant : ℝ := 13 / (120 * Real.sqrt 2)

theorem quadratic_nonneg {Q : Gram} (hQ : Q.PosSemidef) (x : Vec) :
    0 ≤ quadratic Q x := by
  simpa [quadratic] using hQ.2 x

theorem nearest_bddBelow {Q : Gram} (hQ : Q.PosSemidef) (x : Vec) :
    BddBelow (range fun z : IntVec => quadratic Q (x - castVec z)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact quadratic_nonneg hQ _

theorem nearest_nonneg {Q : Gram} (hQ : Q.PosSemidef) (x : Vec) :
    0 ≤ nearest Q x := by
  apply le_ciInf
  intro z
  exact quadratic_nonneg hQ _

theorem nearest_le {Q : Gram} (hQ : Q.PosSemidef) (x : Vec) (z : IntVec) :
    nearest Q x ≤ quadratic Q (x - castVec z) :=
  ciInf_le (nearest_bddBelow hQ x) z

theorem nearest_le_quadratic {Q : Gram} (hQ : Q.PosSemidef) (x : Vec) :
    nearest Q x ≤ quadratic Q x := by
  simpa [castVec, Pi.sub_def] using nearest_le hQ x (fun _ => 0)

theorem nearest_at_integer {Q : Gram} (hQ : Q.PosSemidef) (z : IntVec) :
    nearest Q (castVec z) = 0 := by
  apply le_antisymm _ (nearest_nonneg hQ _)
  simpa [quadratic] using nearest_le hQ (castVec z) z

/-- Integer translation invariance is proved for the infinite infimum. -/
theorem nearest_integer_translate (Q : Gram) (x : Vec) (k : IntVec) :
    nearest Q (x + castVec k) = nearest Q x := by
  unfold nearest
  refine (Equiv.addRight (-k)).iInf_congr ?_
  intro z
  congr 1
  ext i
  simp [castVec]
  ring

theorem quadratic_continuous (Q : Gram) : Continuous (quadratic Q) := by
  unfold quadratic dotProduct Matrix.mulVec
  fun_prop

theorem nearest_measurable (Q : Gram) : Measurable (nearest Q) := by
  apply Measurable.iInf
  intro z
  exact ((quadratic_continuous Q).comp (continuous_id.sub continuous_const)).measurable

/-- In particular, the integral definition is not using the value assigned to a
nonintegrable function: the genuine nearest-point function is integrable. -/
theorem nearest_integrableOn {Q : Gram} (hQ : Q.PosSemidef) :
    IntegrableOn (nearest Q) unitCube := by
  apply ((quadratic_continuous Q).continuousOn.integrableOn_Icc).mono'
    (nearest_measurable Q).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (nearest_nonneg hQ x)]
  exact nearest_le_quadratic hQ x

theorem unitCube_volume : volume unitCube = 1 := by
  simp [unitCube, Real.volume_Icc_pi]

theorem moment_nonneg {Q : Gram} (hQ : Q.PosSemidef) : 0 ≤ moment Q := by
  apply integral_nonneg
  exact nearest_nonneg hQ

theorem normalizedMoment_nonneg {Q : Gram} (hQ : Q.PosDef) :
    0 ≤ normalizedMoment Q := by
  exact div_nonneg (moment_nonneg hQ.posSemidef)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hQ.det_pos.le _))

theorem quadratic_smul (Q : Gram) (c : ℝ) (x : Vec) :
    quadratic (c • Q) x = c * quadratic Q x := by
  simp [quadratic, Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]

theorem nearest_smul {Q : Gram} (hQ : Q.PosSemidef) {c : ℝ} (hc : 0 < c)
    (x : Vec) : nearest (c • Q) x = c * nearest Q x := by
  unfold nearest
  simp_rw [quadratic_smul]
  exact ((OrderIso.mulLeft₀ c hc).map_ciInf (nearest_bddBelow hQ x)).symm

theorem moment_smul {Q : Gram} (hQ : Q.PosSemidef) {c : ℝ} (hc : 0 < c) :
    moment (c • Q) = c * moment Q := by
  unfold moment
  simp_rw [nearest_smul hQ hc]
  exact integral_const_mul c _

/-- Similarity under positive scaling of the Gram matrix, for the analytic integral. -/
theorem normalizedMoment_smul {Q : Gram} (hQ : Q.PosDef) {c : ℝ} (hc : 0 < c) :
    normalizedMoment (c • Q) = normalizedMoment Q := by
  have hpow : (c ^ 4) ^ (1 / 4 : ℝ) = c := by
    rw [← Real.rpow_natCast c 4, ← Real.rpow_mul hc.le]
    norm_num
  unfold normalizedMoment
  rw [moment_smul hQ.posSemidef hc, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [Real.mul_rpow (pow_nonneg hc.le _) hQ.det_pos.le, hpow]
  field_simp [hc.ne', (Real.rpow_pos_of_pos hQ.det_pos (1/4 : ℝ)).ne']; ring

theorem optimalConstant_pos : 0 < optimalConstant := by
  unfold optimalConstant
  positivity

/-- OPEN TARGET: this declaration is a proposition, NOT a theorem or axiom.
Its proof still requires the classification and geometric moment formulas. -/
def MainLowerBound : Prop :=
  ∀ Q : Gram, Q.PosDef → optimalConstant ≤ normalizedMoment Q

end D4.Analytic
