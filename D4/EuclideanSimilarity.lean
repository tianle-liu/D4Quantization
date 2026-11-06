import D4.FullRankLattice
import D4.IntegralCongruence

/-! Actual orthogonal similarities and integer changes of lattice basis. -/
noncomputable section
open Matrix Set
open scoped InnerProductSpace
namespace D4.Euclidean
open Analytic

theorem gram_mul (B C : Gram) : gram (B*C) = C.transpose * gram B * C := by
  unfold gram
  rw [Matrix.transpose_mul]
  noncomm_ring

theorem gram_smul (r : ℝ) (B : Gram) : gram (r • B) = r^2 • gram B := by
  simp only [gram, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]

theorem realization_mul (B C : Gram) (x : Vec) :
    realization (B*C) x = realization B (C *ᵥ x) := by
  simp only [realization, Matrix.mulVec_mulVec]

theorem realization_smul (r : ℝ) (B : Gram) (x : Vec) :
    realization (r • B) x = r • realization B x := by
  change (EuclideanSpace.equiv (Fin 4) ℝ).symm ((r • B) *ᵥ x) = _
  rw [Matrix.smul_mulVec_assoc, map_smul]
  rfl

theorem lattice_smul (r : ℝ) (B : Gram) :
    lattice (r • B) = (fun p : Point => r • p) '' lattice B := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨realization B (castVec z), ⟨z, rfl⟩, (realization_smul r B _).symm⟩
  · rintro ⟨p, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, realization_smul r B _⟩

theorem lattice_unimodular_right (B : Gram) (U : IntegerMatrix) (hU : IsUnit U.det) :
    lattice (B * realMatrix U) = lattice B := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨U *ᵥ z, ?_⟩
    dsimp only
    rw [realization_mul, ← castVec_mulVec]
  · rintro ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := (integerBasisEquiv U hU).surjective z
    refine ⟨w, ?_⟩
    dsimp only
    rw [realization_mul, ← castVec_mulVec]
    change realization B (castVec (integerBasisEquiv U hU w)) = _
    rw [hw]

def gramIsometry {B C : Gram} (hB : B.det ≠ 0) (hC : C.det ≠ 0)
    (h : gram B = gram C) : Point ≃ₗᵢ[ℝ] Point :=
  { (realizationEquiv B hB).symm.toLinearEquiv.trans (realizationEquiv C hC).toLinearEquiv with
    norm_map' := by
      intro p
      obtain ⟨x, rfl⟩ := (realizationEquiv B hB).surjective p
      change ‖realizationEquiv C hC ((realizationEquiv B hB).symm (realizationEquiv B hB x))‖ = _
      rw [ContinuousLinearEquiv.symm_apply_apply]
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simp only [realizationEquiv_apply, norm_sq_realization, h] }

theorem gramIsometry_apply {B C : Gram} (hB : B.det ≠ 0) (hC : C.det ≠ 0)
    (h : gram B = gram C) (x : Vec) :
    gramIsometry hB hC h (realization B x) = realization C x := by
  change realizationEquiv C hC ((realizationEquiv B hB).symm (realizationEquiv B hB x)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem gramIsometry_image_lattice {B C : Gram} (hB : B.det ≠ 0) (hC : C.det ≠ 0)
    (h : gram B = gram C) : gramIsometry hB hC h '' lattice B = lattice C := by
  ext p
  constructor
  · rintro ⟨q, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, (gramIsometry_apply hB hC h _).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨realization B (castVec z), ⟨z, rfl⟩, gramIsometry_apply hB hC h _⟩

/-- Similarity means a positive dilation and an actual Euclidean linear isometry. -/
def SimilarLattices (s t : Set Point) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ O : Point ≃ₗᵢ[ℝ] Point, t = (fun p => r • O p) '' s

theorem similarLattices_of_similarD4Gram {B : Gram} (hB : B.det ≠ 0)
    (h : SimilarD4Gram (gram B)) : SimilarLattices (lattice (basisMatrix ℝ)) (lattice B) := by
  obtain ⟨c, hc, U, hU, hg⟩ := h
  let C : Gram := Real.sqrt c • (basisMatrix ℝ * realMatrix U)
  have hC : C.det ≠ 0 := by
    dsimp [C]
    rw [Matrix.det_smul, Matrix.det_mul, det_basisMatrix]
    exact mul_ne_zero (pow_ne_zero _ (Real.sqrt_pos.mpr hc).ne')
      (mul_ne_zero (by norm_num) (isUnit_iff_ne_zero.mp (realMatrix_det_isUnit U hU)))
  have hgram : gram C = gram B := by
    rw [hg]
    dsimp only [C]
    rw [gram_smul, gram_mul, gram, basisMatrix_transpose_mul, Real.sq_sqrt hc.le]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  let O := gramIsometry hC hB hgram
  refine ⟨Real.sqrt c, Real.sqrt_pos.mpr hc, O, ?_⟩
  have hl : lattice C = (fun p : Point => Real.sqrt c • p) '' lattice (basisMatrix ℝ) := by
    dsimp only [C]
    rw [lattice_smul, lattice_unimodular_right _ U hU]
  have ho := gramIsometry_image_lattice hC hB hgram
  rw [hl, image_image] at ho
  simpa only [Function.comp_def, map_smul, O] using ho.symm

theorem exists_integer_matrix_of_lattice_subset {B C : Gram}
    (h : lattice B ⊆ lattice C) : ∃ U : IntegerMatrix, B = C * realMatrix U := by
  have hc (j : Fin 4) : ∃ z : IntVec,
      realization C (castVec z) = realization B (castVec (Pi.single j 1)) :=
    h ⟨Pi.single j 1, rfl⟩
  choose z hz using hc
  let U : IntegerMatrix := fun i j => z j i
  refine ⟨U, ?_⟩
  apply Matrix.ext_of_mulVec_single
  intro j
  have hs : castVec (Pi.single j (1 : ℤ)) = Pi.single j (1 : ℝ) := by
    ext i
    simp [castVec, Pi.single_apply]
  have hu : realMatrix U *ᵥ Pi.single j (1 : ℝ) = castVec (z j) := by
    rw [Matrix.mulVec_single_one]
    rfl
  have hh := congrArg (WithLp.equiv 2 Vec) (hz j)
  simp only [realization, Equiv.apply_symm_apply, hs] at hh
  rw [← Matrix.mulVec_mulVec, hu]
  exact hh.symm

/-- Equality of two full integer images produces a genuinely unimodular integer basis change. -/
theorem exists_unimodular_of_lattice_eq {B C : Gram} (hB : B.det ≠ 0)
    (h : lattice B = lattice C) :
    ∃ U : IntegerMatrix, IsUnit U.det ∧ B = C * realMatrix U := by
  obtain ⟨U, hU⟩ := exists_integer_matrix_of_lattice_subset h.le
  obtain ⟨V, hV⟩ := exists_integer_matrix_of_lattice_subset h.ge
  have hr : realMatrix V * realMatrix U = 1 := by
    calc
      realMatrix V * realMatrix U = B⁻¹ * (B * (realMatrix V * realMatrix U)) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB), Matrix.one_mul]
      _ = B⁻¹ * B := by rw [← Matrix.mul_assoc B, ← hV, ← hU]
      _ = 1 := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB)
  have hi : V*U = 1 := by
    have hh : realMatrix (V*U) = realMatrix 1 := by
      rwa [realMatrix_mul, realMatrix_one]
    ext i j
    have he := congrFun (congrFun hh i) j
    change (((V*U) i j : ℤ) : ℝ) = (((1 : IntegerMatrix) i j : ℤ) : ℝ) at he
    exact_mod_cast he
  have hdet : V.det * U.det = 1 := by
    rw [← Matrix.det_mul, hi, Matrix.det_one]
  exact ⟨U, isUnit_of_mul_eq_one_right _ _ hdet, hU⟩

def orthogonalCoordinateEquiv (O : Point ≃ₗᵢ[ℝ] Point) : Vec ≃ₗ[ℝ] Vec :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm.toLinearEquiv.trans
    (O.toLinearEquiv.trans (EuclideanSpace.equiv (Fin 4) ℝ).toLinearEquiv)

def orthogonalMatrix (O : Point ≃ₗᵢ[ℝ] Point) : Gram :=
  LinearMap.toMatrix' (orthogonalCoordinateEquiv O).toLinearMap

theorem orthogonalMatrix_mulVec (O : Point ≃ₗᵢ[ℝ] Point) (x : Vec) :
    orthogonalMatrix O *ᵥ x = orthogonalCoordinateEquiv O x := by
  change Matrix.toLin' (LinearMap.toMatrix' (orthogonalCoordinateEquiv O).toLinearMap) x = _
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem realization_orthogonal_mul (O : Point ≃ₗᵢ[ℝ] Point) (B : Gram) (x : Vec) :
    realization (orthogonalMatrix O * B) x = O (realization B x) := by
  unfold realization
  rw [← Matrix.mulVec_mulVec, orthogonalMatrix_mulVec]
  exact (EuclideanSpace.equiv (Fin 4) ℝ).symm_apply_apply _

theorem gram_entry_inner (B : Gram) (i j : Fin 4) :
    gram B i j = ⟪realization B (Pi.single i 1), realization B (Pi.single j 1)⟫_ℝ := by
  simp [gram, realization, EuclideanSpace.inner_piLp_equiv_symm, Matrix.mulVec_single_one,
    Matrix.mul_apply, dotProduct, mul_comm]

theorem gram_orthogonal_mul (O : Point ≃ₗᵢ[ℝ] Point) (B : Gram) :
    gram (orthogonalMatrix O * B) = gram B := by
  ext i j
  simp only [gram_entry_inner, realization_orthogonal_mul, O.inner_map_map]

theorem lattice_orthogonal_mul (O : Point ≃ₗᵢ[ℝ] Point) (B : Gram) :
    lattice (orthogonalMatrix O * B) = O '' lattice B := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨realization B (castVec z), ⟨z, rfl⟩, (realization_orthogonal_mul O B _).symm⟩
  · rintro ⟨p, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, realization_orthogonal_mul O B _⟩

theorem similarD4Gram_of_similarLattices {B : Gram} (hB : B.det ≠ 0)
    (h : SimilarLattices (lattice (basisMatrix ℝ)) (lattice B)) : SimilarD4Gram (gram B) := by
  obtain ⟨r, hr, O, hO⟩ := h
  let C : Gram := r • (orthogonalMatrix O * basisMatrix ℝ)
  have hl : lattice B = lattice C := by
    dsimp only [C]
    rw [lattice_smul, lattice_orthogonal_mul, image_image]
    exact hO
  obtain ⟨U, hU, he⟩ := exists_unimodular_of_lattice_eq hB hl
  refine ⟨r^2, sq_pos_of_pos hr, U, hU, ?_⟩
  rw [he, gram_mul]
  dsimp only [C]
  rw [gram_smul, gram_orthogonal_mul, gram, basisMatrix_transpose_mul]

/-- The matrix equality case is exactly similarity of the physical Euclidean lattices. -/
theorem similarD4Gram_iff_similarLattices {B : Gram} (hB : B.det ≠ 0) :
    SimilarD4Gram (gram B) ↔ SimilarLattices (lattice (basisMatrix ℝ)) (lattice B) :=
  ⟨similarLattices_of_similarD4Gram hB, similarD4Gram_of_similarLattices hB⟩

end D4.Euclidean
