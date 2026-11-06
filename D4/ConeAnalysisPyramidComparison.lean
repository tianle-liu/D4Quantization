import D4.ConeAnalysisPyramid
import D4.ConeAnalysisBound

/-! The comparison for actual pyramids with a positive continuous radial
base. Its right side uses the actual weighted base integral; identifying
that integral as spherical solid angle is kept as a distinct obligation. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory MeasureTheory.Measure ConePerspective

theorem radialBody_subset_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : sphere (0:E) 1 → ℝ) (M : ℝ) (hb : ∀ u, ρ u ≤ M) :
    radialBody ρ ⊆ closedBall (0:E) M := by
  rintro x ⟨y, hy, rfl⟩
  rw [mem_closedBall_zero_iff]
  change ‖y.1‖ < ρ ((homeomorphUnitSphereProd E y).1) at hy
  exact hy.le.trans (hb _)

theorem radialPyramid_volume_expectation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ρ : sphere (0:E) 1 → ℝ) (hρ : Measurable ρ)
    (hp : ∀ u, 0 < ρ u) (M : ℝ) (hM : 0 < M) (hb : ∀ u, ρ u ≤ M) :
    (μ.prod volume).real (pyramid (radialBody ρ)) =
      ∫ u, coneVolume (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1)) (ρ u)
        ∂uniformSphere μ := by
  rw [pyramid_volume μ (radialBody_measurable ρ hρ) hM.le
    (radialBody_subset_closedBall ρ M hb),
    radialBody_volume_expectation μ ρ hρ hp M hM hb]
  unfold coneVolume
  simp only [add_sub_cancel_right, Real.rpow_natCast, integral_const_mul]
  ring

theorem radialPyramid_secondMoment_expectation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ρ : sphere (0:E) 1 → ℝ) (hρ : Continuous ρ)
    (hp : ∀ u, 0 < ρ u) (M : ℝ) (hM : 0 < M) (hb : ∀ u, ρ u ≤ M) :
    (∫ p in pyramid (radialBody ρ), (‖p.1‖^2+p.2^2) ∂μ.prod volume) =
      ∫ u, coneMoment (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1)) (ρ u)
        ∂uniformSphere μ := by
  let k := Module.finrank ℝ E
  let κ := μ.real (ball (0:E) 1)
  rw [pyramid_secondMoment μ (radialBody_measurable ρ hρ.measurable) hM.le
    (radialBody_subset_closedBall ρ M hb),
    radialBody_secondMoment_expectation μ ρ hρ.measurable hp M hM hb,
    radialBody_volume_expectation μ ρ hρ.measurable hp M hM hb]
  have he : (fun u => coneMoment ((k:ℝ)+1) κ (ρ u)) =
      fun u => κ/((k:ℝ)+3)*(ρ u^k+(k:ℝ)/((k:ℝ)+2)*ρ u^(k+2)) := by
    funext u
    unfold coneMoment coneVolume CircularCone.alpha
    rw [add_sub_cancel_right, Real.rpow_natCast, pow_add]
    field_simp
    ring
  change _ = ∫ u, coneMoment ((k:ℝ)+1) κ (ρ u) ∂uniformSphere μ
  rw [he, integral_const_mul]
  have hk : Integrable (fun u => ρ u^k) (uniformSphere μ) :=
    (hρ.pow k).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have hk2 : Integrable (fun u => ρ u^(k+2)) (uniformSphere μ) :=
    (hρ.pow (k+2)).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  rw [integral_add hk (hk2.const_mul _), integral_const_mul]
  dsimp only [k, κ]
  ring

theorem radialPyramid_perspective_comparison {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ρ : sphere (0:E) 1 → ℝ) (hρ : Continuous ρ) (hp : ∀ u, 0 < ρ u) :
    momentPerspective (Module.finrank ℝ E+1)
      ((μ.prod volume).real (pyramid (radialBody ρ)))
      (∫ p in pyramid (radialBody ρ), (‖p.1‖^2+p.2^2) ∂μ.prod volume) ≤
    profile (Module.finrank ℝ E+1)
      (profileConstant (Module.finrank ℝ E+1) (μ.real (ball (0:E) 1)))
      ((Module.finrank ℝ E:ℝ)*μ.real (ball (0:E) 1))
      (∫ y in radialBody ρ, (1+‖y‖^2)^(-((Module.finrank ℝ E:ℝ)+1)/2) ∂μ) := by
  letI : Nonempty (sphere (0:E) 1) := (NormedSpace.sphere_nonempty.mpr zero_le_one).coe_sort
  obtain ⟨u, _, humax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hρ.continuousOn
  have hb : ∀ v, ρ v ≤ ρ u := fun v => humax (mem_univ v)
  rw [radialPyramid_volume_expectation μ ρ hρ.measurable hp (ρ u) (hp u) hb,
    radialPyramid_secondMoment_expectation μ ρ hρ hp (ρ u) (hp u) hb,
    radialBody_angle_expectation μ ρ hρ.measurable hp (ρ u) (hp u) hb]
  have hn : 2 ≤ Module.finrank ℝ E+1 := by
    have := Module.finrank_pos (R:=ℝ) (M:=E)
    omega
  have H := radial_average_comparison (uniformSphere μ) (Module.finrank ℝ E+1) hn
    (μ.real (ball (0:E) 1)) (unitBall_measure_pos μ) ρ hρ hp
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using H

end D4.ConeAnalysis
