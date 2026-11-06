import D4.EuclideanMoment
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
Every discrete full-rank integer submodule of Euclidean four-space is
represented by an invertible real matrix. Thus matrix quantification does
not restrict the class of lattices in the geometric theorem.
-/
noncomputable section
open Matrix Module MeasureTheory Set
namespace D4.Euclidean
open Analytic

def integerLatticeBasis (L : Submodule ℤ Point) [DiscreteTopology L] [IsZLattice ℝ L] :
    Basis (Fin 4) ℤ L := by
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let e : Module.Free.ChooseBasisIndex ℤ L ≃ Fin 4 :=
    Fintype.equivOfCardEq (by
      rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ]
      simp)
  exact (Module.Free.chooseBasis ℤ L).reindex e

def latticeCoordinateEquiv (L : Submodule ℤ Point) [DiscreteTopology L] [IsZLattice ℝ L] :
    Vec ≃ₗ[ℝ] Vec :=
  ((integerLatticeBasis L).ofZLatticeBasis ℝ L).equivFun.symm.trans
    (EuclideanSpace.equiv (Fin 4) ℝ).toLinearEquiv

def latticeBasisMatrix (L : Submodule ℤ Point) [DiscreteTopology L] [IsZLattice ℝ L] : Gram :=
  LinearMap.toMatrix' (latticeCoordinateEquiv L).toLinearMap

theorem latticeBasisMatrix_mulVec (L : Submodule ℤ Point) [DiscreteTopology L] [IsZLattice ℝ L]
    (x : Vec) : latticeBasisMatrix L *ᵥ x = latticeCoordinateEquiv L x := by
  change Matrix.toLin' (LinearMap.toMatrix' (latticeCoordinateEquiv L).toLinearMap) x = _
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem latticeBasisMatrix_det_ne_zero (L : Submodule ℤ Point)
    [DiscreteTopology L] [IsZLattice ℝ L] : (latticeBasisMatrix L).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y h
  apply (latticeCoordinateEquiv L).injective
  simpa only [latticeBasisMatrix_mulVec] using h

theorem realization_latticeBasisMatrix (L : Submodule ℤ Point)
    [DiscreteTopology L] [IsZLattice ℝ L] (x : Vec) :
    realization (latticeBasisMatrix L) x =
      ((integerLatticeBasis L).ofZLatticeBasis ℝ L).equivFun.symm x := by
  unfold realization
  rw [latticeBasisMatrix_mulVec]
  exact (EuclideanSpace.equiv (Fin 4) ℝ).symm_apply_apply _

theorem realBasis_integer_coordinates (L : Submodule ℤ Point)
    [DiscreteTopology L] [IsZLattice ℝ L] (z : IntVec) :
    ((integerLatticeBasis L).ofZLatticeBasis ℝ L).equivFun.symm (castVec z) =
      ((integerLatticeBasis L).equivFun.symm z : L) := by
  apply ((integerLatticeBasis L).ofZLatticeBasis ℝ L).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  ext i
  rw [Basis.equivFun_apply, Basis.ofZLatticeBasis_repr_apply]
  change (z i : ℝ) = ((integerLatticeBasis L).equivFun
    ((integerLatticeBasis L).equivFun.symm z) i : ℝ)
  rw [LinearEquiv.apply_symm_apply]

/-- The matrix image equals the entire given lattice, including all integer points. -/
theorem latticeBasisMatrix_lattice (L : Submodule ℤ Point)
    [DiscreteTopology L] [IsZLattice ℝ L] : lattice (latticeBasisMatrix L) = (L : Set Point) := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    dsimp only
    rw [realization_latticeBasisMatrix, realBasis_integer_coordinates]
    exact Subtype.mem _
  · intro hp
    refine ⟨(integerLatticeBasis L).equivFun ⟨p, hp⟩, ?_⟩
    dsimp only
    rw [realization_latticeBasisMatrix, realBasis_integer_coordinates,
      LinearEquiv.symm_apply_apply]

theorem exists_matrix_of_fullRankLattice (L : Submodule ℤ Point)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ B : Gram, B.det ≠ 0 ∧ lattice B = (L : Set Point) :=
  ⟨latticeBasisMatrix L, latticeBasisMatrix_det_ne_zero L, latticeBasisMatrix_lattice L⟩

def latticeCell (L : Submodule ℤ Point) : Set Point :=
  {p | ∀ q ∈ L, ‖p‖ ≤ ‖p-q‖}

def latticeNormalizedMoment (L : Submodule ℤ Point) : ℝ :=
  (∫ p in latticeCell L, ‖p‖^2) / (4 * (volume (latticeCell L)).toReal ^ (3/2 : ℝ))

theorem latticeCell_eq (L : Submodule ℤ Point)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    latticeCell L = cell (latticeBasisMatrix L) := by
  simp only [latticeCell, cell, latticeBasisMatrix_lattice]
  rfl

theorem latticeNormalizedMoment_eq (L : Submodule ℤ Point)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    latticeNormalizedMoment L = normalizedMoment (gram (latticeBasisMatrix L)) := by
  unfold latticeNormalizedMoment
  rw [latticeCell_eq]
  exact normalizedCellMoment_eq (latticeBasisMatrix_det_ne_zero L)

end D4.Euclidean
