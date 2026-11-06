import D4.SecondaryDomainsSpace
import D4.BasisChange

/-! Positive definiteness is equivalent under integral changes of basis. -/
noncomputable section
namespace D4.Delaunay
open Analytic Matrix

theorem symmetricCongruence_posDef_iff (Q : SymGram) (U : IntegerMatrix)
    (hU : IsUnit U.det) :
    (symmetricCongruence (realMatrix U) Q).val.PosDef ↔ Q.val.PosDef := by
  constructor
  · intro h
    have hb := h.conjTranspose_mul_mul_same (realBasisEquiv U hU).symm.injective
    have he := (symmetricCongruenceHomeomorph (realMatrix U)
      (realMatrix_det_isUnit U hU)).symm_apply_apply Q
    have hm : ((realMatrix U)⁻¹)ᵀ *
        ((realMatrix U)ᵀ * Q.val * realMatrix U) * (realMatrix U)⁻¹ = Q.val :=
      congrArg Subtype.val he
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, symmetricCongruence, hm] using hb
  · intro h
    exact posDef_unimodular_congruence h U hU

end D4.Delaunay
