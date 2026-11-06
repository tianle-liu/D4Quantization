import D4.ConeAnalysisFacetCoordinates
import D4.ConeAnalysisScaling
import D4.ConeAnalysisConvexBase
import D4.ConeAnalysisProjection
import D4.VoronoiPyramids

/-! The actual Voronoi facet pyramid in orthogonal coordinates, with the
facet distance scaled to one. All sets below are the geometrically
defined sets, rather than prescribed volume and moment formulas. -/
noncomputable section
set_option linter.unusedSectionVars false
namespace D4.ConeAnalysis
open Set Metric MeasureTheory D4.FacetGeometry
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def facetHeight (z : E) : ℝ := ‖z‖/2

theorem facetHeight_pos {z : E} (hz : z ≠ 0) : 0 < facetHeight z :=
  div_pos (norm_pos_iff.mpr hz) (by norm_num)

def normalizedFacetBase (L : Submodule ℤ E) (z : E) : Set (tangent z) :=
  (facetHeight z)⁻¹ • base L z

theorem facetHeight_smul_unitNormal {z : E} (hz : z ≠ 0) :
    facetHeight z • unitNormal z = (1/2:ℝ) • z := by
  rw [unitNormal, smul_smul]
  congr 1
  dsimp [facetHeight]
  field_simp [norm_ne_zero_iff.mpr hz]
  ring

theorem normalizedFacetBase_convex (L : Submodule ℤ E) (z : E) :
    Convex ℝ (normalizedFacetBase L z) := (base_convex L z).smul _

theorem normalizedFacetBase_compact (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (z : E) :
    IsCompact (normalizedFacetBase L z) := (base_compact_full (L:=L) z).smul _

theorem normalizedFacetBase_zero_interior {L : Submodule ℤ E} {z : E}
    (hz : IsFacetVector L z) : (0 : tangent z) ∈ interior (normalizedFacetBase L z) := by
  rw [normalizedFacetBase, interior_smul₀ (inv_ne_zero (facetHeight_pos hz.2.1).ne')]
  exact ⟨0, facet_center_interior hz, smul_zero _⟩

theorem facet_pyramid_eq_scaled_coordinates (L : Submodule ℤ E) {z : E} (hz : z ≠ 0) :
    D4.FacetGeometry.pyramid L z = facetHeight z •
      (unitJoinProduct hz '' D4.ConeAnalysis.pyramid (normalizedFacetBase L z)) := by
  rw [pyramid_eq_base_image]
  ext x
  constructor
  · rintro ⟨t, ht, y, hy, rfl⟩
    let p : tangent z × ℝ := (t • ((facetHeight z)⁻¹ • y), t)
    have hp : p ∈ D4.ConeAnalysis.pyramid (normalizedFacetBase L z) := by
      refine ⟨ht, ?_⟩
      change t⁻¹ • (t • ((facetHeight z)⁻¹ • y)) ∈ normalizedFacetBase L z
      rw [inv_smul_smul₀ ht.1.ne']
      exact ⟨y, hy, rfl⟩
    refine ⟨unitJoinProduct hz p, ⟨p, hp, rfl⟩, ?_⟩
    dsimp only
    rw [unitJoinProduct_apply]
    dsimp only [p]
    simp only [Submodule.coe_smul]
    rw [smul_add, smul_comm (facetHeight z) t,
      smul_inv_smul₀ (facetHeight_pos hz).ne', smul_comm (facetHeight z) t,
      facetHeight_smul_unitNormal hz, smul_add]
    abel
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    obtain ⟨y, hy, he⟩ := hp.2
    dsimp only at he
    have he' : p.1 = p.2 • ((facetHeight z)⁻¹ • y) := by
      rw [he, smul_inv_smul₀ hp.1.1.ne']
    refine ⟨p.2, hp.1, y, hy, ?_⟩
    dsimp only
    rw [unitJoinProduct_apply, he', Submodule.coe_smul, Submodule.coe_smul,
      smul_add, smul_comm (facetHeight z) p.2,
      smul_inv_smul₀ (facetHeight_pos hz).ne', smul_comm (facetHeight z) p.2,
      facetHeight_smul_unitNormal hz, smul_add]
    abel

theorem unitJoinProduct_real_volume {z : E} (hz : z ≠ 0)
    (S : Set (tangent z × ℝ)) :
    volume.real (unitJoinProduct hz '' S) =
      ((volume : Measure (tangent z)).prod volume).real S := by
  have H := integral_unitJoinProduct_image hz S (fun _ => (1:ℝ))
  simpa only [integral_const, smul_eq_mul, mul_one, measureReal_def,
    Measure.restrict_apply_univ] using H

theorem facet_pyramid_volume (L : Submodule ℤ E) {z : E} (hz : z ≠ 0) :
    volume.real (D4.FacetGeometry.pyramid L z) =
      (facetHeight z)^(Module.finrank ℝ E) *
        ((volume : Measure (tangent z)).prod volume).real
          (D4.ConeAnalysis.pyramid (normalizedFacetBase L z)) := by
  rw [facet_pyramid_eq_scaled_coordinates L hz,
    real_measure_smul volume _ _ (facetHeight_pos hz).le,
    unitJoinProduct_real_volume hz]

theorem facet_pyramid_secondMoment (L : Submodule ℤ E) {z : E} (hz : z ≠ 0) :
    (∫ x in D4.FacetGeometry.pyramid L z, ‖x‖^2) =
      (facetHeight z)^(Module.finrank ℝ E+2) *
        (∫ p in D4.ConeAnalysis.pyramid (normalizedFacetBase L z), ‖p.1‖^2+p.2^2
          ∂((volume : Measure (tangent z)).prod volume)) := by
  rw [facet_pyramid_eq_scaled_coordinates L hz,
    secondMoment_smul volume _ _ (facetHeight_pos hz),
    integral_unitJoinProduct_image hz]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => unitJoinProduct_norm_sq hz p)

theorem facet_pyramid_perspective (L : Submodule ℤ E) {z : E} (hz : z ≠ 0) :
    ConePerspective.momentPerspective (Module.finrank ℝ E)
      (volume.real (D4.FacetGeometry.pyramid L z))
      (∫ x in D4.FacetGeometry.pyramid L z, ‖x‖^2) =
    ConePerspective.momentPerspective (Module.finrank ℝ E)
      (((volume : Measure (tangent z)).prod volume).real
        (D4.ConeAnalysis.pyramid (normalizedFacetBase L z)))
      (∫ p in D4.ConeAnalysis.pyramid (normalizedFacetBase L z), ‖p.1‖^2+p.2^2
        ∂((volume : Measure (tangent z)).prod volume)) := by
  rw [facet_pyramid_volume L hz, facet_pyramid_secondMoment L hz]
  have H := momentPerspective_scale_nonneg (Module.finrank ℝ E)
    (((volume : Measure (tangent z)).prod volume).real
      (D4.ConeAnalysis.pyramid (normalizedFacetBase L z)))
    (∫ p in D4.ConeAnalysis.pyramid (normalizedFacetBase L z), ‖p.1‖^2+p.2^2
      ∂((volume : Measure (tangent z)).prod volume))
    (facetHeight z) measureReal_nonneg
    (integral_nonneg (fun p => add_nonneg (sq_nonneg _) (sq_nonneg _))) (facetHeight_pos hz)
  rw [show (Module.finrank ℝ E:ℝ)+2 = ((Module.finrank ℝ E+2:ℕ):ℝ) by norm_num,
    Real.rpow_natCast, Real.rpow_natCast] at H
  exact H

theorem facet_pyramid_perspective_comparison {L : Submodule ℤ E}
    [DiscreteTopology L] [IsZLattice ℝ L] {z : E}
    (hz : IsFacetVector L z) (hd : 2 ≤ Module.finrank ℝ E) :
    ConePerspective.momentPerspective (Module.finrank ℝ E)
      (volume.real (D4.FacetGeometry.pyramid L z))
      (∫ x in D4.FacetGeometry.pyramid L z, ‖x‖^2) ≤
    profile (Module.finrank ℝ E)
      (profileConstant (Module.finrank ℝ E) (volume.real (ball (0 : tangent z) 1)))
      ((Module.finrank ℝ (tangent z):ℝ)*volume.real (ball (0 : tangent z) 1))
      (∫ y in normalizedFacetBase L z, (1+‖y‖^2)^(-(Module.finrank ℝ E:ℝ)/2)) := by
  have hdim := tangent_finrank hz.2.1
  have hpos : 0 < Module.finrank ℝ (tangent z) := by omega
  letI : Nontrivial (tangent z) := Module.finrank_pos_iff.mp hpos
  have he : (Module.finrank ℝ E:ℝ) = (Module.finrank ℝ (tangent z):ℝ)+1 := by
    exact_mod_cast hdim.symm
  rw [facet_pyramid_perspective L hz.2.1, ← hdim]
  simpa only [Nat.cast_add, Nat.cast_one] using convexPyramid_perspective_comparison volume
    (normalizedFacetBase_convex L z) (normalizedFacetBase_compact L z)
    (normalizedFacetBase_zero_interior hz)

end D4.ConeAnalysis
