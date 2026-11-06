import D4.VoronoiQuantizer
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Gram coordinates and integer lattices in arbitrary finite dimension. -/
noncomputable section
open Matrix Module MeasureTheory Set
namespace D4.GramCoordinates

abbrev Coord (n : ℕ) := Fin n → ℝ
abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Form (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def realize {n : ℕ} (B : Form n) (x : Coord n) : Point n :=
  (WithLp.equiv 2 (Coord n)).symm (B *ᵥ x)

def gram {n : ℕ} (B : Form n) : Form n := Bᵀ * B

def coordinateEquiv {n : ℕ} (B : Form n) (hB : B.det ≠ 0) :
    Coord n ≃ₗ[ℝ] Coord n :=
  { B.mulVecLin with
    invFun := B⁻¹.mulVec
    left_inv := fun x => by
      change B⁻¹ *ᵥ (B *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB),
        Matrix.one_mulVec]
    right_inv := fun x => by
      change B *ᵥ (B⁻¹ *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB),
        Matrix.one_mulVec] }

def realizeEquiv {n : ℕ} (B : Form n) (hB : B.det ≠ 0) : Coord n ≃L[ℝ] Point n :=
  (coordinateEquiv B hB).toContinuousLinearEquiv.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

@[simp] theorem realizeEquiv_apply {n : ℕ} (B : Form n) (hB : B.det ≠ 0) (x : Coord n) :
    realizeEquiv B hB x = realize B x := rfl

def columnBasis {n : ℕ} (B : Form n) (hB : B.det ≠ 0) : Basis (Fin n) ℝ (Point n) :=
  (Pi.basisFun ℝ (Fin n)).map (realizeEquiv B hB).toLinearEquiv

def lattice {n : ℕ} (B : Form n) (hB : B.det ≠ 0) : Submodule ℤ (Point n) :=
  Submodule.span ℤ (Set.range (columnBasis B hB))

instance {n : ℕ} (B : Form n) (hB : B.det ≠ 0) : DiscreteTopology (lattice B hB) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (columnBasis B hB))))

instance {n : ℕ} (B : Form n) (hB : B.det ≠ 0) : IsZLattice ℝ (lattice B hB) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (columnBasis B hB))))

@[simp] theorem columnBasis_repr_realize {n : ℕ} (B : Form n) (hB : B.det ≠ 0)
    (x : Coord n) (i : Fin n) : (columnBasis B hB).repr (realize B x) i = x i := by
  change ((Pi.basisFun ℝ (Fin n)).map (realizeEquiv B hB).toLinearEquiv).repr
    (realizeEquiv B hB x) i = x i
  simp only [Basis.map_repr, Pi.basisFun_repr]
  change (realizeEquiv B hB).symm (realizeEquiv B hB x) i = x i
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem lattice_eq_integer_image {n : ℕ} (B : Form n) (hB : B.det ≠ 0) :
    (lattice B hB : Set (Point n)) =
      Set.range (fun z : Fin n → ℤ => realize B (fun i => (z i : ℝ))) := by
  ext p
  constructor
  · intro hp
    have hh := ((columnBasis B hB).mem_span_iff_repr_mem ℤ p).mp hp
    choose z hz using hh
    refine ⟨z, ?_⟩
    apply (columnBasis B hB).ext_elem
    intro i
    simpa using hz i
  · rintro ⟨z, rfl⟩
    apply ((columnBasis B hB).mem_span_iff_repr_mem ℤ _).mpr
    intro i
    exact ⟨z i, by simp⟩

theorem realize_sub {n : ℕ} (B : Form n) (x y : Coord n) :
    realize B (x-y) = realize B x-realize B y := by
  apply (WithLp.equiv 2 (Coord n)).injective
  exact Matrix.mulVec_sub B x y

theorem norm_sq_realize {n : ℕ} (B : Form n) (x : Coord n) :
    ‖realize B x‖^2 = x ⬝ᵥ (gram B *ᵥ x) := by
  rw [← real_inner_self_eq_norm_sq]
  unfold realize
  rw [EuclideanSpace.inner_piLp_equiv_symm]
  simp only [star_trivial]
  unfold gram
  symm
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem map_realize_volume {n : ℕ} (B : Form n) (hB : B.det ≠ 0) :
    Measure.map (realize B) volume = ENNReal.ofReal |B.det|⁻¹ • volume := by
  have hm : Measurable (Matrix.toLin' B) :=
    (coordinateEquiv B hB).toContinuousLinearEquiv.continuous.measurable
  change Measure.map ((WithLp.equiv 2 (Coord n)).symm ∘ Matrix.toLin' B) volume = _
  rw [← Measure.map_map (PiLp.volume_preserving_equiv_symm (Fin n)).measurable hm,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hB, Measure.map_smul,
    (PiLp.volume_preserving_equiv_symm (Fin n)).map_eq]
  rw [abs_inv]

end D4.GramCoordinates
