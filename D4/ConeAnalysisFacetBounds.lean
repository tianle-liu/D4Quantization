import D4.ConeAnalysisFacetAngle

/-! Positivity and the open angular range for actual Voronoi facets. -/
noncomputable section
set_option linter.unusedSectionVars false
namespace D4.ConeAnalysis
open Set Metric MeasureTheory D4.FacetGeometry

theorem compact_convex_angle_mem {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    {B : Set F} (hc : Convex ℝ B) (hB : IsCompact B) (h0 : (0:F) ∈ interior B) :
    (∫ y in B, (1+‖y‖^2)^(-((Module.finrank ℝ F:ℝ)+1)/2) ∂μ) ∈
      Ioo 0 (angle (Module.finrank ℝ F+1)
        ((Module.finrank ℝ F:ℝ)*μ.real (ball (0:F) 1)) (Real.pi/2)) := by
  letI : Nonempty (sphere (0:F) 1) := (NormedSpace.sphere_nonempty.mpr zero_le_one).coe_sort
  let ρ := gaugeRadius B
  have hp : ∀ u, 0 < ρ u := gaugeRadius_pos hB.isBounded h0
  have hρ : Continuous ρ := gaugeRadius_continuous hc hB.isBounded h0
  obtain ⟨umax, _, hmaxρ⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hρ.continuousOn
  let D := (Module.finrank ℝ F:ℝ)*μ.real (ball (0:F) 1)
  let ω := fun u => radiusAngle (Module.finrank ℝ F+1) D (ρ u)
  have hn : 2 ≤ Module.finrank ℝ F+1 := by have := Module.finrank_pos (R:=ℝ) (M:=F); omega
  have hD : 0 < D := mul_pos (by exact_mod_cast Module.finrank_pos (R:=ℝ) (M:=F))
    (unitBall_measure_pos μ)
  have hω : Continuous ω := (continuous_iff_continuousAt.mpr fun r =>
    (hasDerivAt_radiusAngle (Module.finrank ℝ F+1) D r).continuousAt).comp hρ
  have hi : Integrable ω (uniformSphere μ) :=
    hω.integrable_of_hasCompactSupport (isClosed_tsupport ω).isCompact
  have hr : ∀ u, ω u ∈ Ioo 0 (angle (Module.finrank ℝ F+1) D (Real.pi/2)) := by
    intro u
    rw [← radiusAngle_image_positive (Module.finrank ℝ F+1) hn D hD]
    exact ⟨ρ u, hp u, rfl⟩
  obtain ⟨umin, _, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hω.continuousOn
  obtain ⟨umax', _, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hω.continuousOn
  have hlo : ω umin ≤ ∫ u, ω u ∂uniformSphere μ := by
    simpa using integral_mono (integrable_const (ω umin)) hi (fun u => hmin (mem_univ u))
  have hhi : (∫ u, ω u ∂uniformSphere μ) ≤ ω umax' := by
    simpa using integral_mono hi (integrable_const (ω umax')) (fun u => hmax (mem_univ u))
  have he : (∫ y in B, (1+‖y‖^2)^(-((Module.finrank ℝ F:ℝ)+1)/2) ∂μ) =
      ∫ u, ω u ∂uniformSphere μ := by
    calc
      _ = ∫ y in radialBody ρ, (1+‖y‖^2)^(-((Module.finrank ℝ F:ℝ)+1)/2) ∂μ :=
        setIntegral_congr_set (radialBody_gaugeRadius_ae μ hc hB.isBounded h0).symm
      _ = _ := radialBody_angle_expectation μ ρ hρ.measurable hp (ρ umax) (hp umax)
        (fun u => hmaxρ (mem_univ u))
  rw [he]
  exact ⟨(hr umin).1.trans_le hlo, hhi.trans_lt (hr umax').2⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {z : E}

theorem normalizedFacetBase_volume_pos (hz : IsFacetVector L z) :
    0 < volume.real (normalizedFacetBase L z) := by
  have hp : 0 < volume (normalizedFacetBase L z) :=
    (isOpen_interior.measure_pos volume ⟨0, normalizedFacetBase_zero_interior hz⟩).trans_le
      (measure_mono interior_subset)
  exact ENNReal.toReal_pos hp.ne' (normalizedFacetBase_compact L z).measure_lt_top.ne

theorem facet_pyramid_volume_pos (hz : IsFacetVector L z) :
    0 < volume.real (D4.FacetGeometry.pyramid L z) := by
  rw [facet_pyramid_volume L hz.2.1]
  obtain ⟨M, hM, hb⟩ := (normalizedFacetBase_compact L z).isBounded.subset_closedBall_lt
    0 (0 : tangent z)
  rw [pyramid_volume volume (normalizedFacetBase_compact L z).measurableSet hM.le hb]
  exact mul_pos (pow_pos (facetHeight_pos hz.2.1) _)
    (div_pos (normalizedFacetBase_volume_pos hz) (by positivity))

theorem facet_pyramid_secondMoment_pos (hz : IsFacetVector L z) :
    0 < ∫ x in D4.FacetGeometry.pyramid L z, ‖x‖^2 := by
  rw [facet_pyramid_secondMoment L hz.2.1]
  obtain ⟨M, hM, hb⟩ := (normalizedFacetBase_compact L z).isBounded.subset_closedBall_lt
    0 (0 : tangent z)
  rw [pyramid_secondMoment volume (normalizedFacetBase_compact L z).measurableSet hM.le hb]
  apply mul_pos (pow_pos (facetHeight_pos hz.2.1) _)
  exact div_pos (add_pos_of_nonneg_of_pos (integral_nonneg fun y => sq_nonneg ‖y‖)
    (normalizedFacetBase_volume_pos hz)) (by positivity)

theorem facetSolidAngle_mem (hz : IsFacetVector L z) (hd : 2 ≤ Module.finrank ℝ E) :
    facetSolidAngle L z ∈ Ioo 0 (angle (Module.finrank ℝ E)
      ((Module.finrank ℝ (tangent z):ℝ)*volume.real (ball (0 : tangent z) 1)) (Real.pi/2)) := by
  have hdim := tangent_finrank hz.2.1
  have hpos : 0 < Module.finrank ℝ (tangent z) := by omega
  letI : Nontrivial (tangent z) := Module.finrank_pos_iff.mp hpos
  rw [facetSolidAngle_eq_base_integral L hz.2.1, ← hdim]
  simpa only [Nat.cast_add, Nat.cast_one] using compact_convex_angle_mem volume
    (normalizedFacetBase_convex L z) (normalizedFacetBase_compact L z)
    (normalizedFacetBase_zero_interior hz)

end D4.ConeAnalysis
