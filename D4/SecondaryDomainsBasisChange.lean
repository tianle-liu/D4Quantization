import D4.SecondaryDomainsType
import D4.MomentBasisChange

/-! Integral changes of coordinates preserve the complete actual Delaunay type. -/
noncomputable section
namespace D4.Delaunay
open Analytic Principal Matrix MeasureTheory Set

def planePrecomp (R : Gram) (p : AffineSlack) : AffineSlack :=
  ⟨Rᵀ *ᵥ p.normal, p.offset⟩

theorem planePrecomp_eval (R : Gram) (p : AffineSlack) (x : Vec) :
    (planePrecomp R p).eval x = p.eval (R *ᵥ x) := by
  simp only [planePrecomp, AffineSlack.eval, Matrix.dotProduct_mulVec]
  rw [← Matrix.vecMul_transpose Rᵀ p.normal, Matrix.transpose_transpose]

theorem realBasisEquiv_symm_castVec (U : IntegerMatrix) (hU : IsUnit U.det) (z : IntVec) :
    (realBasisEquiv U hU).symm (castVec z) =
      castVec ((integerBasisEquiv U hU).symm z) := by
  apply (realBasisEquiv U hU).injective
  rw [LinearEquiv.apply_symm_apply, realBasisEquiv_castVec, LinearEquiv.apply_symm_apply]

theorem quadratic_congruence_integer (Q : Gram) (U : IntegerMatrix)
    (hU : IsUnit U.det) (z : IntVec) :
    quadratic ((realMatrix U)ᵀ * Q * realMatrix U) (castVec z) =
      quadratic Q (castVec (integerBasisEquiv U hU z)) := by
  rw [quadratic_congruence, ← realBasisEquiv_apply U hU, realBasisEquiv_castVec]

theorem latticeHull_image_basis (U : IntegerMatrix) (hU : IsUnit U.det)
    (F : Finset IntVec) :
    latticeHull (F.image (integerBasisEquiv U hU)) =
      (realBasisEquiv U hU) '' latticeHull F := by
  have hs : castVec '' (↑(F.image (integerBasisEquiv U hU)) : Set IntVec) =
      (realBasisEquiv U hU) '' (castVec '' (F : Set IntVec)) := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨castVec v,⟨v,hv,rfl⟩,realBasisEquiv_castVec U hU v⟩
    · rintro ⟨y,⟨v,hv,rfl⟩,rfl⟩
      exact ⟨integerBasisEquiv U hU v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,
        (realBasisEquiv_castVec U hU v).symm⟩
  unfold latticeHull
  rw [hs]
  exact ((realBasisEquiv U hU).toLinearMap.image_convexHull _).symm

theorem latticeHull_image_basis_volume (U : IntegerMatrix) (hU : IsUnit U.det)
    (F : Finset IntVec) :
    volume (latticeHull (F.image (integerBasisEquiv U hU))) = volume (latticeHull F) := by
  rw [latticeHull_image_basis]
  have h := (basisMeasurableEquiv_preserving U hU).measure_preimage_equiv
    ((basisMeasurableEquiv U hU) '' latticeHull F)
  rw [Set.preimage_image_eq _ (basisMeasurableEquiv U hU).injective] at h
  exact h.symm

theorem tightPlane_basis_forward {Q : Gram} {F : Finset IntVec} {p : AffineSlack}
    (U : IntegerMatrix) (hU : IsUnit U.det)
    (hp : TightPlane ((realMatrix U)ᵀ * Q * realMatrix U) F p) :
    TightPlane Q (F.image (integerBasisEquiv U hU))
      (planePrecomp ((realMatrix U)⁻¹) p) := by
  have he (n : IntVec) : (planePrecomp ((realMatrix U)⁻¹) p).eval (castVec n) =
      p.eval (castVec ((integerBasisEquiv U hU).symm n)) := by
    rw [planePrecomp_eval, ← realBasisEquiv_symm_apply U hU,
      realBasisEquiv_symm_castVec]
  have hq (n : IntVec) :
      quadratic ((realMatrix U)ᵀ * Q * realMatrix U)
        (castVec ((integerBasisEquiv U hU).symm n)) = quadratic Q (castVec n) := by
    rw [quadratic_congruence_integer Q U hU, LinearEquiv.apply_symm_apply]
  constructor
  · intro n
    rw [he, ← hq]
    exact hp.1 _
  · intro n
    rw [he, ← hq, hp.2]
    constructor
    · intro hn
      exact Finset.mem_image.mpr ⟨_,hn,LinearEquiv.apply_symm_apply _ _⟩
    · intro hn
      obtain ⟨z,hz,hzn⟩ := Finset.mem_image.mp hn
      rw [← hzn, LinearEquiv.symm_apply_apply]
      exact hz

theorem tightPlane_basis_backward {Q : Gram} {F : Finset IntVec} {p : AffineSlack}
    (U : IntegerMatrix) (hU : IsUnit U.det)
    (hp : TightPlane Q (F.image (integerBasisEquiv U hU)) p) :
    TightPlane ((realMatrix U)ᵀ * Q * realMatrix U) F (planePrecomp (realMatrix U) p) := by
  have he (n : IntVec) : (planePrecomp (realMatrix U) p).eval (castVec n) =
      p.eval (castVec (integerBasisEquiv U hU n)) := by
    rw [planePrecomp_eval, ← realBasisEquiv_apply U hU, realBasisEquiv_castVec]
  constructor
  · intro n
    rw [he, quadratic_congruence_integer Q U hU]
    exact hp.1 _
  · intro n
    rw [he, quadratic_congruence_integer Q U hU, hp.2]
    constructor
    · intro hn
      obtain ⟨z,hz,hzn⟩ := Finset.mem_image.mp hn
      exact (integerBasisEquiv U hU).injective hzn ▸ hz
    · intro hn
      exact Finset.mem_image.mpr ⟨n,hn,rfl⟩

theorem delaunayType_basis_change (Q : Gram) (U : IntegerMatrix)
    (hU : IsUnit U.det) (F : Finset IntVec) :
    F ∈ delaunayType ((realMatrix U)ᵀ * Q * realMatrix U) ↔
      F.image (integerBasisEquiv U hU) ∈ delaunayType Q := by
  constructor
  · rintro ⟨⟨p,hp⟩,hv⟩
    refine ⟨⟨_,tightPlane_basis_forward U hU hp⟩,?_⟩
    rwa [latticeHull_image_basis_volume]
  · rintro ⟨⟨p,hp⟩,hv⟩
    refine ⟨⟨_,tightPlane_basis_backward U hU hp⟩,?_⟩
    rwa [latticeHull_image_basis_volume] at hv

end D4.Delaunay
