import D4.FundamentalDomain

/-! The total volume of integer-periodic almost-disjoint pieces inside one
unit period equals the sum of their original volumes. -/
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

theorem window_volume_periodization (W : Set Vec) :
    volume W=∑' n : IntVec,volume (unitCube ∩ (n+ᵥW)) := by
  rw [halfOpenCube_fundamental.measure_eq_tsum W]
  apply tsum_congr
  intro n
  rw [inter_comm]
  apply measure_congr
  exact ae_eq_set_inter halfOpenCube_ae_unitCube Filter.EventuallyEq.rfl

def periodicPieces {ι : Type*} (W : ι → Set Vec) (p : ι×IntVec) : Set Vec := p.2+ᵥW p.1

theorem periodic_packing_volume {ι : Type*} [Fintype ι]
    (W : ι → Set Vec) (hm : ∀ i,MeasurableSet (W i))
    (hd : Pairwise fun p q : ι×IntVec => AEDisjoint volume (periodicPieces W p) (periodicPieces W q)) :
    volume (unitCube ∩ ⋃ p,periodicPieces W p)=∑ i,volume (W i) := by
  classical
  rw [inter_iUnion]
  have hpieces (p : ι×IntVec) : MeasurableSet (periodicPieces W p) :=
    (hm p.1).const_vadd p.2
  rw [measure_iUnion₀ (fun p q hpq =>
    (hd hpq).mono inter_subset_right inter_subset_right)
    (fun p => ((show MeasurableSet unitCube from isCompact_Icc.measurableSet).inter (hpieces p)).nullMeasurableSet)]
  rw [ENNReal.tsum_prod',tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact (window_volume_periodization (W i)).symm

end D4.Analytic
