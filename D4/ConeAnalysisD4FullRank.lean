import D4.ConeAnalysisD4Radial
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The actual even-sum lattice is discrete and spans real four-space. -/
noncomputable section
namespace D4.PhysicalD4
open Set Matrix Euclidean Analytic

def physicalBasisEquiv : Vec ≃ₗ[ℝ] Point :=
  (LinearEquiv.ofBijective (basisMatrix ℝ).mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det (basisMatrix ℝ)).mpr (by rw [det_basisMatrix]; norm_num)),
     Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det (basisMatrix ℝ)).mpr (by rw [det_basisMatrix]; norm_num))⟩).trans
    (EuclideanSpace.equiv (Fin 4) ℝ).symm.toLinearEquiv

theorem physicalBasisEquiv_apply (x : Vec) :
    physicalBasisEquiv x=realization (basisMatrix ℝ) x := rfl

def physicalBasis : Basis (Fin 4) ℝ Point := Basis.ofEquivFun physicalBasisEquiv.symm

theorem physicalBasis_repr (x : Point) (i : Fin 4) :
    physicalBasis.repr x i=physicalBasisEquiv.symm x i :=
  Basis.ofEquivFun_repr_apply _ _ _

theorem lattice_eq_span_physicalBasis : lattice=Submodule.span ℤ (Set.range physicalBasis) := by
  ext x
  rw [← SetLike.mem_coe, lattice_eq_basis_lattice]
  constructor
  · rintro ⟨z,rfl⟩
    apply (physicalBasis.mem_span_iff_repr_mem ℤ _).mpr
    intro i
    refine ⟨z i,?_⟩
    change (z i : ℝ)=physicalBasis.repr (realization (basisMatrix ℝ) (castVec z)) i
    rw [physicalBasis_repr,← physicalBasisEquiv_apply,LinearEquiv.symm_apply_apply]
    rfl
  · intro hx
    have hh := (physicalBasis.mem_span_iff_repr_mem ℤ x).mp hx
    choose z hz using hh
    refine ⟨z,?_⟩
    change realization (basisMatrix ℝ) (castVec z)=x
    rw [← physicalBasisEquiv_apply]
    apply physicalBasisEquiv.symm.injective
    rw [LinearEquiv.symm_apply_apply]
    ext i
    exact (hz i).trans (physicalBasis_repr x i)

instance lattice_discreteTopology : DiscreteTopology lattice := by
  rw [lattice_eq_span_physicalBasis]
  infer_instance

instance lattice_isZLattice : IsZLattice ℝ lattice where
  span_top := by
    rw [lattice_eq_span_physicalBasis]
    exact ZSpan.span_top physicalBasis

end D4.PhysicalD4
