import D4.EuclideanSimilarity
import D4.VoronoiFacetGeometry

/-! Equal volumes of D4 similarities force one common positive scale.
The volume is that of the actual Euclidean Voronoi cell. -/
noncomputable section
namespace D4.Blocks
open Matrix Set MeasureTheory Analytic Euclidean

theorem voronoi_volume_similarD4 (L : Submodule ℤ Point) (r : ℝ) (hr : 0 < r)
    (O : Point ≃ₗᵢ[ℝ] Point)
    (hL : (L : Set Point) = (fun p => r • O p) '' lattice (basisMatrix ℝ)) :
    volume.real (FacetGeometry.voronoi L) = 2*r^4 := by
  let C : Gram := orthogonalMatrix O * basisMatrix ℝ
  have hg : C.det^2 = 4 := by
    have h := congrArg Matrix.det (gram_orthogonal_mul O (basisMatrix ℝ))
    norm_num only [C,gram,Matrix.det_mul,Matrix.det_transpose,det_basisMatrix,pow_two] at h ⊢
    exact h
  have habs : |C.det| = 2 := by
    nlinarith [sq_abs C.det,abs_nonneg C.det]
  have habsR : |(r • C).det| = 2*r^4 := by
    rw [Matrix.det_smul,Fintype.card_fin,abs_mul,abs_pow,abs_of_pos hr,habs]
    ring
  have hdet : (r • C).det ≠ 0 := by
    apply abs_pos.mp
    rw [habsR]
    positivity
  have hlat : lattice (r • C) = (L : Set Point) := by
    dsimp only [C]
    rw [lattice_smul,lattice_orthogonal_mul,image_image]
    exact hL.symm
  have hcell : FacetGeometry.voronoi L = cell (r • C) := by
    unfold FacetGeometry.voronoi cell
    rw [hlat]
    rfl
  rw [hcell,measureReal_def,cell_volume hdet,ENNReal.toReal_ofReal (abs_nonneg _),habsR]

/-- The equality condition in the orthogonal-block application has the
literal common-scale form stated in the paper. Each block may have its own
orthogonal transformation. No moment formula is assumed in this bridge. -/
theorem similarD4_equal_volumes_iff_common_scale {ι : Type*} [Nonempty ι]
    (L : ι → Submodule ℤ Point) :
    ((∀ i, SimilarLattices (lattice (basisMatrix ℝ)) (L i : Set Point)) ∧
      (∀ i j, volume.real (FacetGeometry.voronoi (L i)) =
        volume.real (FacetGeometry.voronoi (L j)))) ↔
    ∃ r : ℝ, 0 < r ∧ ∃ O : ι → Point ≃ₗᵢ[ℝ] Point,
      ∀ i, (L i : Set Point) = (fun p => r • O i p) '' lattice (basisMatrix ℝ) := by
  classical
  constructor
  · rintro ⟨hs,hv⟩
    choose r hr O hO using hs
    let i₀ : ι := Classical.choice inferInstance
    have he (i : ι) : r i = r i₀ := by
      have h := hv i i₀
      rw [voronoi_volume_similarD4 (L i) (r i) (hr i) (O i) (hO i),
        voronoi_volume_similarD4 (L i₀) (r i₀) (hr i₀) (O i₀) (hO i₀)] at h
      apply (pow_left_inj₀ (hr i).le (hr i₀).le (by norm_num : (4 : ℕ) ≠ 0)).mp
      linarith
    refine ⟨r i₀,hr i₀,O,fun i => ?_⟩
    rw [← he i]
    exact hO i
  · rintro ⟨r,hr,O,hO⟩
    refine ⟨fun i => ⟨r,hr,O i,hO i⟩,fun i j => ?_⟩
    rw [voronoi_volume_similarD4 (L i) r hr (O i) (hO i),
      voronoi_volume_similarD4 (L j) r hr (O j) (hO j)]

end D4.Blocks
