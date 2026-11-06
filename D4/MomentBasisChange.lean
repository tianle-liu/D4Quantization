import D4.BasisChange
import D4.FundamentalDomain

/-!
# Integer basis invariance of the actual moment integral

This proof combines the bijection on all integer competitors, a genuine
change of variables for Lebesgue measure, and the fundamental-domain
integral theorem. No moment-polynomial identity is assumed.
-/
noncomputable section
open Matrix MeasureTheory Set
namespace D4
open Analytic

def basisMeasurableEquiv (U : IntegerMatrix) (hU : IsUnit U.det) : Vec ≃ᵐ Vec :=
  (realBasisEquiv U hU).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

@[simp] theorem basisMeasurableEquiv_apply (U : IntegerMatrix) (hU : IsUnit U.det) (x : Vec) :
    basisMeasurableEquiv U hU x = realMatrix U *ᵥ x := rfl

theorem basisMeasurableEquiv_preserving (U : IntegerMatrix) (hU : IsUnit U.det) :
    MeasurePreserving (basisMeasurableEquiv U hU) volume volume := by
  refine ⟨(basisMeasurableEquiv U hU).measurable, ?_⟩
  change Measure.map (Matrix.toLin' (realMatrix U)) volume = volume
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (realMatrix_det_isUnit U hU).ne_zero]
  rw [abs_inv, abs_det_realMatrix U hU]
  simp

theorem moment_unimodular (Q : RealGram) (U : IntegerMatrix) (hU : IsUnit U.det) :
    moment ((realMatrix U).transpose * Q * realMatrix U) = moment Q := by
  unfold moment
  simp_rw [nearest_unimodular Q U hU]
  apply integral_nearest_comp_equiv Q (basisMeasurableEquiv U hU)
    (basisMeasurableEquiv_preserving U hU) (integerBasisEquiv U hU).toEquiv
  intro z x
  change realBasisEquiv U hU (castVec z + x) =
    castVec (integerBasisEquiv U hU z) + realBasisEquiv U hU x
  rw [map_add, realBasisEquiv_castVec]

theorem normalizedMoment_unimodular (Q : RealGram) (U : IntegerMatrix) (hU : IsUnit U.det) :
    normalizedMoment ((realMatrix U).transpose * Q * realMatrix U) = normalizedMoment Q := by
  unfold normalizedMoment
  rw [moment_unimodular Q U hU, det_unimodular_congruence Q U hU]

theorem normalizedMoment_integralCongruent {Q R : RealGram} (h : IntegralCongruent Q R) :
    normalizedMoment R = normalizedMoment Q := by
  obtain ⟨U, hU, rfl⟩ := h
  exact normalizedMoment_unimodular Q U hU

end D4
