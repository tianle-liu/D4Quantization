import D4.PeriodicLocalization

/-! Periodic integration counts a localized window exactly once per period.
The equality is for the actual nearest-point function and actual set integrals. -/
noncomputable section
namespace D4.Analytic
open Set Matrix MeasureTheory
open scoped Pointwise
attribute [local instance] integerTranslation

local instance : MeasurableConstVAdd IntVec Vec where
  measurable_const_vadd _ := (continuous_const.add continuous_id).measurable
local instance : MeasurableVAdd IntVec Vec where
  measurable_const_vadd _ := (continuous_const.add continuous_id).measurable
  measurable_vadd_const _ := measurable_of_countable _
local instance : VAddInvariantMeasure IntVec Vec volume where
  measure_preimage_vadd z s _ := measure_preimage_add volume (castVec z) s

def shiftedCube (c : Vec) : Set Vec := (fun x => x-c) ⁻¹' unitCube
def shiftedHalfCube (c : Vec) : Set Vec := (fun x => x-c) ⁻¹' halfOpenCube

theorem shiftedHalfCube_fundamental (c : Vec) :
    IsAddFundamentalDomain IntVec (shiftedHalfCube c) volume := by
  apply halfOpenCube_fundamental.preimage_of_equiv
    (measurePreserving_sub_right volume c).quasiMeasurePreserving (e := fun z : IntVec => z)
    Function.bijective_id
  intro z x
  change castVec z+x-c=castVec z+(x-c)
  abel

theorem shiftedCube_ae (c : Vec) : shiftedHalfCube c=ᵐ[volume] shiftedCube c :=
  (measurePreserving_sub_right volume c).quasiMeasurePreserving.ae_eq_comp halfOpenCube_ae_unitCube

theorem nearest_window_periodization (Q : Gram) (c : Vec) (W : Set Vec)
    (hf : IntegrableOn (nearest Q) W) :
    (∫ x in W,nearest Q x)=
      ∑' n : IntVec,∫ x in (n+ᵥW) ∩ shiftedCube c,nearest Q x := by
  have h := (shiftedHalfCube_fundamental c).setIntegral_eq_tsum' hf
  rw [h]
  apply tsum_congr
  intro n
  have he : ((n+ᵥW) ∩ shiftedHalfCube c : Set Vec)=ᵐ[volume] ((n+ᵥW) ∩ shiftedCube c : Set Vec) :=
    ae_eq_set_inter (Filter.EventuallyEq.rfl) (shiftedCube_ae c)
  rw [setIntegral_congr_set he]
  congr 1
  funext x
  change nearest Q (castVec (-n)+x)=nearest Q x
  simpa only [add_comm] using nearest_integer_translate Q x (-n)

/-- Compact windows need only finitely many terms, uniformly when a family
of windows stays in a fixed bounded region. -/
theorem nearest_window_finite_periodization (Q : Gram) (c : Vec) (W : Set Vec)
    (hf : IntegrableOn (nearest Q) W) (s : Finset IntVec)
    (hs : ∀ n,(shiftedCube c ∩ (n+ᵥW)).Nonempty → n∈s) :
    (∫ x in W,nearest Q x)=
      ∑ n∈s,∫ x in (n+ᵥW) ∩ shiftedCube c,nearest Q x := by
  rw [nearest_window_periodization Q c W hf]
  apply tsum_eq_sum
  intro n hn
  have he : (n+ᵥW) ∩ shiftedCube c=∅ := by
    apply Set.eq_empty_of_forall_not_mem
    intro x hx
    exact hn (hs n ⟨x,hx.2,hx.1⟩)
  simp only [he,setIntegral_empty]

end D4.Analytic
