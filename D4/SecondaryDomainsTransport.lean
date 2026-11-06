import D4.SecondaryDomainsBasisChange
import D4.SecondaryDomainsSpace

/-! Bijective transport of actual Delaunay cell families and equality of types. -/
noncomputable section
namespace D4.Delaunay
open Analytic Principal Matrix Set

def basisFinsetEquiv (U : IntegerMatrix) (hU : IsUnit U.det) :
    Finset IntVec ≃ Finset IntVec :=
  (integerBasisEquiv U hU).toEquiv.finsetCongr

@[simp] theorem basisFinsetEquiv_apply (U : IntegerMatrix) (hU : IsUnit U.det)
    (F : Finset IntVec) :
    basisFinsetEquiv U hU F = F.image (integerBasisEquiv U hU) := by
  simp only [basisFinsetEquiv, Equiv.finsetCongr_apply, Finset.map_eq_image]
  rfl

theorem delaunayType_basisEquiv (Q : Gram) (U : IntegerMatrix)
    (hU : IsUnit U.det) (F : Finset IntVec) :
    F ∈ delaunayType ((realMatrix U)ᵀ * Q * realMatrix U) ↔
      basisFinsetEquiv U hU F ∈ delaunayType Q := by
  rw [basisFinsetEquiv_apply]
  exact delaunayType_basis_change Q U hU F

theorem delaunayType_basis_image (Q : Gram) (U : IntegerMatrix) (hU : IsUnit U.det) :
    (basisFinsetEquiv U hU) '' delaunayType ((realMatrix U)ᵀ * Q * realMatrix U) =
      delaunayType Q := by
  ext F
  constructor
  · rintro ⟨S,hS,rfl⟩
    exact (delaunayType_basisEquiv Q U hU S).mp hS
  · intro hF
    refine ⟨(basisFinsetEquiv U hU).symm F, ?_,
      (basisFinsetEquiv U hU).apply_symm_apply F⟩
    apply (delaunayType_basisEquiv Q U hU _).mpr
    simpa only [Equiv.apply_symm_apply] using hF

theorem delaunayType_congruence_eq_iff (Q R : Gram) (U : IntegerMatrix)
    (hU : IsUnit U.det) :
    delaunayType ((realMatrix U)ᵀ * Q * realMatrix U) =
      delaunayType ((realMatrix U)ᵀ * R * realMatrix U) ↔
      delaunayType Q = delaunayType R := by
  constructor
  · intro h
    rw [← delaunayType_basis_image Q U hU, h, delaunayType_basis_image R U hU]
  · intro h
    ext F
    rw [delaunayType_basisEquiv Q U hU, delaunayType_basisEquiv R U hU, h]

def delaunayCellsBasisEquiv (Q : Gram) (U : IntegerMatrix) (hU : IsUnit U.det) :
    {F // F ∈ delaunayType ((realMatrix U)ᵀ * Q * realMatrix U)} ≃
      {F // F ∈ delaunayType Q} where
  toFun F := ⟨basisFinsetEquiv U hU F.val,
    (delaunayType_basisEquiv Q U hU F.val).mp F.property⟩
  invFun F := ⟨(basisFinsetEquiv U hU).symm F.val,
    (delaunayType_basisEquiv Q U hU _).mpr (by
      simpa only [Equiv.apply_symm_apply] using F.property)⟩
  left_inv F := Subtype.ext ((basisFinsetEquiv U hU).symm_apply_apply F.val)
  right_inv F := Subtype.ext ((basisFinsetEquiv U hU).apply_symm_apply F.val)

theorem exists_delaunayType_basis_transport (Q : Gram) (U : IntegerMatrix)
    (hU : IsUnit U.det) :
    ∃ e : IntVec ≃ₗ[ℤ] IntVec, ∀ F : Finset IntVec,
      F ∈ delaunayType ((realMatrix U)ᵀ * Q * realMatrix U) ↔
        F.image e ∈ delaunayType Q :=
  ⟨integerBasisEquiv U hU, delaunayType_basis_change Q U hU⟩

theorem exists_delaunayCells_basis_equiv (Q : Gram) (U : IntegerMatrix)
    (hU : IsUnit U.det) :
    ∃ e : {F // F ∈ delaunayType ((realMatrix U)ᵀ * Q * realMatrix U)} ≃
        {F // F ∈ delaunayType Q},
      ∀ F, (e F).val = F.val.image (integerBasisEquiv U hU) :=
  ⟨delaunayCellsBasisEquiv Q U hU, fun F => basisFinsetEquiv_apply U hU F.val⟩

end D4.Delaunay
