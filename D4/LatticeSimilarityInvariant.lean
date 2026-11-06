import D4.GeometricTheoremB
import D4.ConeAnalysisUnitDiagonal

/-! Similarity invariance of the actual Voronoi normalized second moment
in every finite dimension. The cell transformation and both integral
transformation laws are proved for the full lattice sets. -/
noncomputable section
namespace D4.FacetGeometry
open Set MeasureTheory
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem mem_voronoi_similarity (L K : Submodule ℤ E) (r : ℝ) (hr : 0 < r)
    (O : E ≃ₗᵢ[ℝ] E) (hK : (K : Set E) = r • (O '' (L : Set E))) (x : E) :
    r • O x ∈ voronoi K ↔ x ∈ voronoi L := by
  constructor
  · intro hx z hz
    have hzK : r • O z ∈ K := by
      change r • O z ∈ (K : Set E)
      rw [hK]
      exact ⟨O z, ⟨z, hz, rfl⟩, rfl⟩
    have H := hx (r • O z) hzK
    simpa only [← smul_sub, ← O.map_sub, norm_smul, O.norm_map,
      Real.norm_eq_abs, abs_of_pos hr, mul_le_mul_left hr] using H
  · intro hx z hz
    change z ∈ (K : Set E) at hz
    rw [hK] at hz
    rcases hz with ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    simpa only [← smul_sub, ← O.map_sub, norm_smul, O.norm_map,
      Real.norm_eq_abs, abs_of_pos hr, mul_le_mul_left hr] using hx w hw

theorem voronoi_similarity (L K : Submodule ℤ E) (r : ℝ) (hr : 0 < r)
    (O : E ≃ₗᵢ[ℝ] E) (hK : (K : Set E) = r • (O '' (L : Set E))) :
    voronoi K = r • (O '' voronoi L) := by
  ext x
  constructor
  · intro hx
    let y := O.symm (r⁻¹ • x)
    have hy : r • O y = x := by simp [y, smul_smul, hr.ne']
    exact ⟨O y, ⟨y, (mem_voronoi_similarity L K r hr O hK y).mp (hy ▸ hx), rfl⟩, hy⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact (mem_voronoi_similarity L K r hr O hK z).mpr hz

theorem isometry_volume (O : E ≃ₗᵢ[ℝ] E) (S : Set E) :
    volume.real (O '' S) = volume.real S := by
  have H := O.measurePreserving.measure_preimage_emb O.toHomeomorph.measurableEmbedding (O '' S)
  rw [Set.preimage_image_eq S O.injective] at H
  exact congrArg ENNReal.toReal H.symm

theorem isometry_secondMoment (O : E ≃ₗᵢ[ℝ] E) (S : Set E) :
    (∫ x in O '' S, ‖x‖^2) = ∫ x in S, ‖x‖^2 := by
  have H := O.measurePreserving.setIntegral_image_emb
    O.toHomeomorph.measurableEmbedding (fun x : E => ‖x‖^2) S
  simpa only [O.norm_map] using H

theorem voronoi_similarity_volume (L K : Submodule ℤ E) (r : ℝ) (hr : 0 < r)
    (O : E ≃ₗᵢ[ℝ] E) (hK : (K : Set E) = r • (O '' (L : Set E))) :
    volume.real (voronoi K) = r^(Module.finrank ℝ E) * volume.real (voronoi L) := by
  rw [voronoi_similarity L K r hr O hK, ConeAnalysis.real_measure_smul volume _ _ hr.le,
    isometry_volume]

theorem voronoi_similarity_secondMoment (L K : Submodule ℤ E) (r : ℝ) (hr : 0 < r)
    (O : E ≃ₗᵢ[ℝ] E) (hK : (K : Set E) = r • (O '' (L : Set E))) :
    (∫ x in voronoi K, ‖x‖^2) =
      r^(Module.finrank ℝ E+2) * (∫ x in voronoi L, ‖x‖^2) := by
  rw [voronoi_similarity L K r hr O hK, ConeAnalysis.secondMoment_smul volume _ _ hr,
    isometry_secondMoment]

/-- The normalized moment is invariant under every positive dilation and
orthogonal linear isometry, in arbitrary finite dimension. -/
theorem normalizedCellMoment_similarity (L K : Submodule ℤ E) (r : ℝ) (hr : 0 < r)
    (O : E ≃ₗᵢ[ℝ] E) (hK : (K : Set E) = r • (O '' (L : Set E))) :
    normalizedCellMoment K = normalizedCellMoment L := by
  by_cases hd : Module.finrank ℝ E = 0
  · simp [normalizedCellMoment, ConePerspective.normalizedMoment, hd]
  unfold normalizedCellMoment
  rw [voronoi_similarity_volume L K r hr O hK, voronoi_similarity_secondMoment L K r hr O hK]
  have hd' : (Module.finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast hd
  have hp : r^((Module.finrank ℝ E : ℝ)+2) = r^(Module.finrank ℝ E+2) := by
    rw [show (Module.finrank ℝ E : ℝ)+2 = ((Module.finrank ℝ E+2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  simpa only [hp, Real.rpow_natCast] using ConeAnalysis.normalizedMoment_scale (Module.finrank ℝ E)
    (volume.real (voronoi L)) (∫ x in voronoi L, ‖x‖^2) r hd'
    ENNReal.toReal_nonneg hr

/-- At fixed positive cell volume, normalized-moment comparison is exactly
second-moment comparison. -/
theorem normalizedCellMoment_le_iff_same_volume (L K : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (hd : 0 < Module.finrank ℝ E)
    (hV : volume.real (voronoi K) = volume.real (voronoi L)) :
    normalizedCellMoment L ≤ normalizedCellMoment K ↔
      (∫ x in voronoi L, ‖x‖^2) ≤ ∫ x in voronoi K, ‖x‖^2 := by
  have hv : 0 < volume.real (voronoi L) :=
    ENNReal.toReal_pos
      (Measure.measure_pos_of_nonempty_interior volume ⟨0,zero_mem_interior_voronoi (L := L)⟩).ne'
      (voronoi_compact_full (L := L)).measure_ne_top
  have hd' : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hd
  unfold normalizedCellMoment ConePerspective.normalizedMoment
  rw [hV]
  exact div_le_div_iff_of_pos_right (mul_pos hd' (Real.rpow_pos_of_pos hv _))

end D4.FacetGeometry
