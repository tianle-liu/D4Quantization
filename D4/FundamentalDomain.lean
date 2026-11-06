import D4.Definitions
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Integration over integer fundamental domains

The half-open cube is proved to be a fundamental domain for *all* integer
translations. This connects the analytic moment definition to the general
fundamental-domain integral theorem, without any polyhedral moment formula.
-/
noncomputable section
open Matrix MeasureTheory Set

namespace D4.Analytic

def integerTranslation : AddAction IntVec Vec where
  vadd z x := castVec z + x
  zero_vadd x := by
    change castVec 0 + x = x
    ext i
    simp [castVec]
  add_vadd z w x := by
    change castVec (z + w) + x = castVec z + (castVec w + x)
    ext i
    simp [castVec]
    ring

attribute [local instance] integerTranslation

@[simp] theorem integer_vadd (z : IntVec) (x : Vec) :
    z +ᵥ x = castVec z + x := rfl

local instance integerTranslation_measurable : MeasurableConstVAdd IntVec Vec where
  measurable_const_vadd _ := (continuous_const.add continuous_id).measurable

local instance integerTranslation_measurable₂ : MeasurableVAdd IntVec Vec where
  measurable_const_vadd _ := (continuous_const.add continuous_id).measurable
  measurable_vadd_const _ := measurable_of_countable _

local instance integerTranslation_invariant : VAddInvariantMeasure IntVec Vec volume where
  measure_preimage_vadd z s hs := by
    change volume ((fun x : Vec => castVec z + x) ⁻¹' s) = volume s
    exact measure_preimage_add volume (castVec z) s

def halfOpenCube : Set Vec := Set.pi Set.univ (fun _ => Ico (0 : ℝ) 1)

theorem halfOpenCube_measurable : MeasurableSet halfOpenCube :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

theorem halfOpenCube_ae_unitCube : halfOpenCube =ᵐ[volume] unitCube := by
  exact Measure.univ_pi_Ico_ae_eq_Icc

theorem halfOpenCube_fundamental : IsAddFundamentalDomain IntVec halfOpenCube volume := by
  apply IsAddFundamentalDomain.mk' halfOpenCube_measurable.nullMeasurableSet
  intro x
  refine ⟨fun i => -⌊x i⌋, ?_, ?_⟩
  · intro i hi
    change 0 ≤ (-⌊x i⌋ : ℤ) + x i ∧ (-⌊x i⌋ : ℤ) + x i < 1
    push_cast
    constructor
    · linarith [Int.floor_le (x i)]
    · linarith [Int.lt_floor_add_one (x i)]
  · intro z hz
    ext i
    have hi := hz i (mem_univ i)
    change 0 ≤ (z i : ℝ) + x i ∧ (z i : ℝ) + x i < 1 at hi
    have he : ⌊x i⌋ = - z i := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith [hi.1, hi.2]
    omega

/-- The closed cube in the definition and the half-open fundamental cube
have the same integral, because their difference has measure zero. -/
theorem moment_eq_halfOpenCube (Q : Gram) :
    moment Q = ∫ x in halfOpenCube, nearest Q x := by
  exact setIntegral_congr_set halfOpenCube_ae_unitCube.symm

/-- The genuine nearest-distance integral is the same on every measurable
fundamental domain for the integer lattice. -/
theorem moment_eq_fundamentalDomain (Q : Gram) {s : Set Vec}
    (hs : IsAddFundamentalDomain IntVec s volume) :
    moment Q = ∫ x in s, nearest Q x := by
  rw [moment_eq_halfOpenCube]
  apply halfOpenCube_fundamental.setIntegral_eq hs
  intro z x
  simpa only [integer_vadd, add_comm] using nearest_integer_translate Q x z

/-- A volume-preserving change of variables that permutes integer translations
preserves the integral of the genuine nearest-distance function. -/
theorem integral_nearest_comp_equiv (Q : Gram) (f : Vec ≃ᵐ Vec)
    (hf : MeasurePreserving f volume volume) (e : IntVec ≃ IntVec)
    (he : ∀ z x, f (castVec z + x) = castVec (e z) + f x) :
    (∫ x in unitCube, nearest Q (f x)) = moment Q := by
  have himage : IsAddFundamentalDomain IntVec (f '' halfOpenCube) volume := by
    apply halfOpenCube_fundamental.image_of_equiv f.toEquiv
      (MeasurePreserving.symm f hf).quasiMeasurePreserving e.symm
    intro z x
    simpa only [integer_vadd, Equiv.apply_symm_apply] using he (e.symm z) x
  calc
    (∫ x in unitCube, nearest Q (f x)) = ∫ x in halfOpenCube, nearest Q (f x) :=
      setIntegral_congr_set halfOpenCube_ae_unitCube.symm
    _ = ∫ x in f '' halfOpenCube, nearest Q x :=
      (hf.setIntegral_image_emb f.measurableEmbedding _ _).symm
    _ = moment Q := (moment_eq_fundamentalDomain Q himage).symm

end D4.Analytic
