import D4.ConeAnalysisFacet
import D4.ConeAnalysisSolidAngle

/-! The angular integral in the cone comparison is the actual spherical
measure of the ray cone over the Voronoi facet. -/
noncomputable section
set_option linter.unusedSectionVars false
namespace D4.ConeAnalysis
open Set Metric MeasureTheory MeasureTheory.Measure D4.FacetGeometry
open scoped Pointwise

def heightCone {F : Type*} [AddCommGroup F] [Module ℝ F] (B : Set F) : Set (F × ℝ) :=
  {p | 0 < p.2 ∧ p.2⁻¹ • p.1 ∈ B}

theorem heightCone_measurable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] {B : Set F} (hB : MeasurableSet B) :
    MeasurableSet (heightCone B) := by
  exact (measurable_snd measurableSet_Ioi).inter
    (hB.preimage (measurable_snd.inv.smul measurable_fst))

theorem heightCone_smul {F : Type*} [AddCommGroup F] [Module ℝ F]
    (B : Set F) {c : ℝ} (hc : 0 < c) (p : F × ℝ) :
    c • p ∈ heightCone B ↔ p ∈ heightCone B := by
  simp only [heightCone, mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    mul_pos_iff_of_pos_left hc, mul_inv_rev, smul_smul]
  have he : p.2⁻¹ * c⁻¹ * c = p.2⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]
  rw [he]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem unitJoinProduct_smul {z : E} (hz : z ≠ 0) (c : ℝ) (p : tangent z × ℝ) :
    unitJoinProduct hz (c • p) = c • unitJoinProduct hz p := by
  simp [unitJoinProduct_apply, smul_add, smul_smul]

theorem unitJoinProduct_heightCone_cap {z : E} (hz : z ≠ 0)
    (B : Set (tangent z)) :
    (unitJoinProduct hz '' heightCone B) ∩ ball (0:E) 1 =
      unitJoinProduct hz '' cappedPyramid B := by
  ext x
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hx⟩
    refine ⟨p, ?_, rfl⟩
    have hn : ‖p.1‖^2+p.2^2 < 1 := by
      rw [← unitJoinProduct_norm_sq hz]
      exact (sq_lt_one_iff₀ (norm_nonneg _)).2 (mem_ball_zero_iff.mp hx)
    refine ⟨⟨⟨hp.1, ?_⟩, hp.2⟩, hn⟩
    nlinarith [sq_nonneg ‖p.1‖]
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, ⟨hp.1.1.1, hp.1.2⟩, rfl⟩, ?_⟩
    rw [mem_ball_zero_iff, ← sq_lt_one_iff₀ (norm_nonneg _), unitJoinProduct_norm_sq hz]
    exact hp.2

theorem unitJoinProduct_heightCone_sphericalMeasure {z : E} (hz : z ≠ 0)
    {B : Set (tangent z)} (hB : IsCompact B) :
    volume.toSphere.real {u : sphere (0:E) 1 | (u:E) ∈ unitJoinProduct hz '' heightCone B} =
      ∫ y in B, (1+‖y‖^2)^(-(Module.finrank ℝ E:ℝ)/2) := by
  let C := unitJoinProduct hz '' heightCone B
  have hC : MeasurableSet C := (unitJoinProduct hz).measurableEmbedding.measurableSet_image.mpr
    (heightCone_measurable hB.measurableSet)
  have hzero : (0:E) ∉ C := by
    rintro ⟨p, hp, he⟩
    have h0 : unitJoinProduct hz (0 : tangent z × ℝ) = 0 := by simp
    have hp0 : p = 0 := (unitJoinProduct hz).injective (he.trans h0.symm)
    subst p
    exact (lt_irrefl 0) hp.1
  have hscale : ∀ (c : ℝ), 0 < c → ∀ x : E, c • x ∈ C ↔ x ∈ C := by
    intro c hc x
    obtain ⟨p, rfl⟩ := (unitJoinProduct hz).surjective x
    rw [← unitJoinProduct_smul, (unitJoinProduct hz).injective.mem_set_image,
      (unitJoinProduct hz).injective.mem_set_image]
    exact heightCone_smul B hc p
  rw [sphericalMeasure_eq_dim_cap volume C hC hzero hscale,
    unitJoinProduct_heightCone_cap hz B, unitJoinProduct_real_volume hz]
  obtain ⟨M, hM, hb⟩ := hB.isBounded.subset_closedBall_lt 0 (0 : tangent z)
  rw [cappedPyramid_volume volume hB.measurableSet hM.le hb]
  have hd : (Module.finrank ℝ E:ℝ) = (Module.finrank ℝ (tangent z):ℝ)+1 := by
    exact_mod_cast (tangent_finrank hz).symm
  rw [hd, mul_div_cancel₀ _ (by positivity : ((Module.finrank ℝ (tangent z):ℝ)+1) ≠ 0)]

def facetRayCone (L : Submodule ℤ E) (z : E) : Set E := Ioi (0:ℝ) • face L z

def facetSolidAngle (L : Submodule ℤ E) (z : E) : ℝ :=
  volume.toSphere.real {u : sphere (0:E) 1 | (u:E) ∈ facetRayCone L z}

theorem unitJoinProduct_base_ray {z : E} (hz : z ≠ 0) (t : ℝ) (y : tangent z) :
    unitJoinProduct hz (t • ((facetHeight z)⁻¹ • y), t) =
      (t / facetHeight z) • ((1/2:ℝ) • z + (y:E)) := by
  apply (smul_right_injective (M:=E) (facetHeight_pos hz).ne')
  rw [unitJoinProduct_apply]
  simp only [Submodule.coe_smul]
  rw [smul_add, smul_comm (facetHeight z) t,
    smul_inv_smul₀ (facetHeight_pos hz).ne', smul_comm (facetHeight z) t,
    facetHeight_smul_unitNormal hz]
  simp only [smul_smul]
  rw [show facetHeight z * (t / facetHeight z) = t by
    field_simp [(facetHeight_pos hz).ne']]
  simp only [smul_add, smul_smul]
  abel

theorem facetRayCone_eq_coordinates (L : Submodule ℤ E) {z : E} (hz : z ≠ 0) :
    facetRayCone L z = unitJoinProduct hz '' heightCone (normalizedFacetBase L z) := by
  rw [facetRayCone, face_eq_base_image]
  ext x
  constructor
  · rintro ⟨t, ht, _, ⟨y, hy, rfl⟩, rfl⟩
    let s := t * facetHeight z
    have hs : 0 < s := mul_pos ht (facetHeight_pos hz)
    refine ⟨(s • ((facetHeight z)⁻¹ • y), s), ⟨hs, ?_⟩, ?_⟩
    · change s⁻¹ • (s • ((facetHeight z)⁻¹ • y)) ∈ normalizedFacetBase L z
      rw [inv_smul_smul₀ hs.ne']
      exact ⟨y, hy, rfl⟩
    · rw [unitJoinProduct_base_ray hz]
      congr 1
      exact mul_div_cancel_right₀ t (facetHeight_pos hz).ne'
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨y, hy, he⟩ := hp.2
    dsimp only at he
    have hp1 : p.1 = p.2 • ((facetHeight z)⁻¹ • y) := by
      rw [he, smul_inv_smul₀ hp.1.ne']
    refine ⟨p.2 / facetHeight z, div_pos hp.1 (facetHeight_pos hz),
      (1/2:ℝ) • z + (y:E), ⟨y, hy, rfl⟩, ?_⟩
    conv_rhs => rw [show p = (p.2 • ((facetHeight z)⁻¹ • y), p.2) by ext <;> simp [hp1]]
    exact (unitJoinProduct_base_ray hz p.2 y).symm

theorem facetSolidAngle_eq_base_integral (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] {z : E} (hz : z ≠ 0) :
    facetSolidAngle L z =
      ∫ y in normalizedFacetBase L z, (1+‖y‖^2)^(-(Module.finrank ℝ E:ℝ)/2) := by
  rw [facetSolidAngle, facetRayCone_eq_coordinates L hz]
  exact unitJoinProduct_heightCone_sphericalMeasure hz (normalizedFacetBase_compact L z)

theorem facet_pyramid_spherical_comparison {L : Submodule ℤ E}
    [DiscreteTopology L] [IsZLattice ℝ L] {z : E}
    (hz : IsFacetVector L z) (hd : 2 ≤ Module.finrank ℝ E) :
    ConePerspective.momentPerspective (Module.finrank ℝ E)
      (volume.real (D4.FacetGeometry.pyramid L z))
      (∫ x in D4.FacetGeometry.pyramid L z, ‖x‖^2) ≤
    profile (Module.finrank ℝ E)
      (profileConstant (Module.finrank ℝ E) (volume.real (ball (0 : tangent z) 1)))
      ((Module.finrank ℝ (tangent z):ℝ)*volume.real (ball (0 : tangent z) 1))
      (facetSolidAngle L z) := by
  rw [facetSolidAngle_eq_base_integral L hz.2.1]
  exact facet_pyramid_perspective_comparison hz hd

end D4.ConeAnalysis
