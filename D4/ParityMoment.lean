import D4.ParityDomain
import D4.PrincipalIntegral
import D4.RayEvaluation
import Mathlib.MeasureTheory.Integral.Pi

/-! Exact integration of the parity quantizer on its genuine fundamental domain. -/
noncomputable section
open Matrix MeasureTheory Set
open scoped ENNReal
namespace D4.Quantizer
open Analytic

theorem centeredCube_eq_Icc : centeredCube = Icc (fun _ => (-1/2 : ℝ)) (fun _ => (1/2 : ℝ)) := by
  ext x
  simp only [centeredCube, Metric.mem_closedBall, dist_zero_right, mem_Icc, Pi.le_def]
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  simp only [Real.norm_eq_abs, abs_le, forall_and, neg_div]

theorem centeredCube_product (f : Fin 4 → ℝ → ℝ) :
    (∫ x in centeredCube, ∏ i, f i (x i)) =
      ∏ i, ∫ t in Icc (-1/2 : ℝ) (1/2), f i t := by
  rw [centeredCube_eq_Icc, ← pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  let μ : Measure ℝ := volume.restrict (Icc (-1/2 : ℝ) (1/2))
  change (∫ x : Vec, ∏ i, f i (x i) ∂Measure.pi (fun _ : Fin 4 => μ)) =
    ∏ i, ∫ t, f i t ∂μ
  letI : MeasureSpace ℝ := ⟨μ⟩
  haveI : SigmaFinite μ := by dsimp [μ]; infer_instance
  exact integral_fintype_prod_eq_prod (Fin 4) f

theorem centered_interval_sq : (∫ t in Icc (-1/2 : ℝ) (1/2), t^2) = 1/12 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  norm_num [integral_pow]

theorem centeredCube_coordinate_sq (i : Fin 4) :
    (∫ x in centeredCube, (x i)^2) = 1/12 := by
  have h := centeredCube_product (fun k t => if k = i then t^2 else 1)
  have hi (k : Fin 4) : (∫ t in Icc (-1/2 : ℝ) (1/2), if k = i then t^2 else 1) =
      if k = i then (1 : ℝ)/12 else 1 := by
    by_cases hk : k = i
    · simpa only [hk, ite_true] using centered_interval_sq
    · simp only [hk, ite_false]
      norm_num
  simp_rw [hi] at h
  simpa only [Finset.prod_ite_eq', Finset.mem_univ, ite_true] using h

theorem squaredError_continuous (z : IntVec) : Continuous (fun x : Vec => squaredError x z) := by
  unfold squaredError
  fun_prop

theorem squaredError_integrableOn_cube (z : IntVec) :
    IntegrableOn (fun x => squaredError x z) centeredCube :=
  (squaredError_continuous z).continuousOn.integrableOn_compact (isCompact_closedBall _ _)

theorem integral_squaredError_centeredCube : (∫ x in centeredCube, squaredError x 0) = 1/3 := by
  simp only [squaredError, Pi.zero_apply, Int.cast_zero, sub_zero]
  rw [integral_finset_sum]
  · simp [centeredCube_coordinate_sq]
    norm_num
  · intro i _
    exact (show Continuous (fun x : Vec => (x i)^2) by
      fun_prop).continuousOn.integrableOn_compact (isCompact_closedBall _ _)

theorem physicalNearest_nonneg (x : Vec) : 0 ≤ physicalNearest x :=
  nearest_nonneg gramMatrix_posDef.posSemidef _

theorem physicalNearest_measurable : Measurable physicalNearest :=
  (nearest_measurable _).comp basisEquiv.symm.toContinuousLinearEquiv.continuous.measurable

theorem physicalNearest_integrableOn_compact {s : Set Vec} (hs : IsCompact s) :
    IntegrableOn physicalNearest s := by
  apply ((squaredError_continuous 0).continuousOn.integrableOn_compact hs).mono'
    physicalNearest_measurable.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (physicalNearest_nonneg x)]
  exact physicalNearest_le x (by simp [evenSumLattice])

theorem integral_physicalNearest_centeredCube :
    (∫ x in centeredCube, physicalNearest x) = 1/3 := by
  rw [setIntegral_congr_fun (show MeasurableSet centeredCube from measurableSet_closedBall)
    (fun x hx => physicalNearest_centeredCube hx)]
  exact integral_squaredError_centeredCube

theorem integral_physicalNearest_oddCube :
    (∫ x in centeredCube, physicalNearest (x + castVec oddUnit)) = 8/15 := by
  rw [setIntegral_congr_fun (show MeasurableSet centeredCube from measurableSet_closedBall)
    (fun x hx => physicalNearest_oddCube hx)]
  have hn : IntegrableOn (fun x : Vec => ‖x‖) centeredCube :=
    continuous_norm.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hc : IntegrableOn (fun _ : Vec => (1 : ℝ)) centeredCube :=
    continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hsum : IntegrableOn (fun x : Vec => squaredError x 0 + 1) centeredCube :=
    (squaredError_integrableOn_cube 0).add hc
  rw [integral_sub hsum (hn.const_mul 2),
    integral_add (squaredError_integrableOn_cube 0) hc, integral_const_mul,
    integral_squaredError_centeredCube, integral_norm_centeredCube, integral_const,
    measureReal_def, Measure.restrict_apply_univ, centeredCube_volume]
  norm_num

def centeredHalfOpenCube : Set Vec := univ.pi (fun _ => Ico (-1/2 : ℝ) (1/2))

theorem centeredHalfOpenCube_measurable : MeasurableSet centeredHalfOpenCube :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

theorem centeredHalfOpenCube_ae : centeredHalfOpenCube =ᵐ[volume] centeredCube := by
  rw [centeredCube_eq_Icc]
  exact Measure.univ_pi_Ico_ae_eq_Icc

theorem centeredHalfOpenCube_subset : centeredHalfOpenCube ⊆ centeredCube := by
  rw [centeredCube_eq_Icc]
  intro x hx
  exact ⟨fun i => (hx i (mem_univ i)).1, fun i => (hx i (mem_univ i)).2.le⟩

def oddHalfOpenCube : Set Vec := (fun x => x + castVec oddUnit) '' centeredHalfOpenCube

theorem parityBox_eq_union : parityBox = centeredHalfOpenCube ∪ oddHalfOpenCube := by
  ext x
  have hu : castVec oddUnit 0 = 1 := by norm_num [castVec, oddUnit]
  have hui (i : Fin 4) (hi : i ≠ 0) : castVec oddUnit i = 0 := by
    simp [castVec, oddUnit, Pi.single_apply, hi, Ne.symm hi]
  constructor
  · intro hx
    by_cases h0 : x 0 < 1/2
    · left
      intro i _
      by_cases hi : i = 0
      · simpa [hi] using And.intro hx.1 h0
      · exact hx.2.2 i hi
    · right
      refine ⟨x-castVec oddUnit, ?_, sub_add_cancel _ _⟩
      intro i _
      change (-1/2 : ℝ) ≤ x i - castVec oddUnit i ∧ x i - castVec oddUnit i < 1/2
      by_cases hi : i = 0
      · rw [hi, hu]
        constructor <;> linarith [hx.1, hx.2.1]
      · simpa only [hui i hi, sub_zero] using hx.2.2 i hi
  · rintro (hx | ⟨y, hy, rfl⟩)
    · have h0 := hx 0 (mem_univ 0)
      exact ⟨h0.1, by linarith [h0.2], fun i _ => hx i (mem_univ i)⟩
    · have h0 := hy 0 (mem_univ 0)
      refine ⟨?_, ?_, ?_⟩
      · change (-1/2 : ℝ) ≤ y 0 + castVec oddUnit 0
        rw [hu]
        linarith [h0.1]
      · change y 0 + castVec oddUnit 0 < (3/2 : ℝ)
        rw [hu]
        linarith [h0.2]
      · intro i hi
        change (-1/2 : ℝ) ≤ y i + castVec oddUnit i ∧ y i + castVec oddUnit i < 1/2
        simpa only [hui i hi, add_zero] using hy i (mem_univ i)

theorem halfOpenCubes_disjoint : Disjoint centeredHalfOpenCube oddHalfOpenCube := by
  apply disjoint_left.mpr
  rintro x hx ⟨y, hy, rfl⟩
  have hx0 := (hx 0 (mem_univ 0)).2
  have hy0 := (hy 0 (mem_univ 0)).1
  change y 0 + castVec oddUnit 0 < (1/2 : ℝ) at hx0
  norm_num [castVec, oddUnit] at hx0
  linarith

theorem oddHalfOpenCube_measurable : MeasurableSet oddHalfOpenCube :=
  (MeasurableEquiv.addRight (castVec oddUnit)).measurableSet_image.mpr
    centeredHalfOpenCube_measurable

theorem physicalNearest_integrableOn_halfCube : IntegrableOn physicalNearest centeredHalfOpenCube :=
  (physicalNearest_integrableOn_compact (isCompact_closedBall _ _)).mono_set
    centeredHalfOpenCube_subset

theorem physicalNearest_integrableOn_oddHalfCube : IntegrableOn physicalNearest oddHalfOpenCube :=
  (physicalNearest_integrableOn_compact
    ((show IsCompact centeredCube from isCompact_closedBall _ _).image
      (continuous_id.add continuous_const))).mono_set (image_mono centeredHalfOpenCube_subset)

theorem integral_physicalNearest_parityBox :
    (∫ x in parityBox, physicalNearest x) = 13/15 := by
  rw [parityBox_eq_union, setIntegral_union halfOpenCubes_disjoint oddHalfOpenCube_measurable
    physicalNearest_integrableOn_halfCube physicalNearest_integrableOn_oddHalfCube]
  have h1 : (∫ x in centeredHalfOpenCube, physicalNearest x) = 1/3 := by
    rw [setIntegral_congr_set centeredHalfOpenCube_ae]
    exact integral_physicalNearest_centeredCube
  have h2 : (∫ x in oddHalfOpenCube, physicalNearest x) = 8/15 := by
    rw [oddHalfOpenCube, (measurePreserving_add_right (volume : Measure Vec)
      (castVec oddUnit)).setIntegral_image_emb
      (MeasurableEquiv.addRight (castVec oddUnit)).measurableEmbedding,
      setIntegral_congr_set centeredHalfOpenCube_ae]
    exact integral_physicalNearest_oddCube
  rw [h1, h2]
  norm_num

theorem moment_eq_half_parityBox :
    moment (gramMatrix ℝ) = (1/2) * ∫ x in parityBox, physicalNearest x := by
  rw [moment_eq_fundamentalDomain _ parityCoordinateDomain_fundamental]
  let e : Vec ≃ᵐ Vec := basisEquiv.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he (x : Vec) : e x = basisMatrix ℝ *ᵥ x := rfl
  have hm : Measure.map e volume = ENNReal.ofReal (1/2 : ℝ) • volume := by
    change Measure.map (Matrix.toLin' (basisMatrix ℝ)) volume = _
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [det_basisMatrix]; norm_num),
      det_basisMatrix]
    norm_num
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  have h := setIntegral_map_equiv (μ := (volume : Measure Vec)) e physicalNearest parityBox
  rw [hm, Measure.restrict_smul, integral_smul_measure] at h
  have hp : (fun x : Vec => physicalNearest (e x)) = nearest (gramMatrix ℝ) := by
    funext x
    change nearest (gramMatrix ℝ) (basisEquiv.symm (basisEquiv x)) = _
    rw [basisEquiv.symm_apply_apply]
  rw [hp] at h
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/2), smul_eq_mul] using h.symm

/-- Exact moment of the paper's D4 Gram matrix, with no geometric formula assumed. -/
theorem moment_gramMatrix : moment (gramMatrix ℝ) = 13/30 := by
  rw [moment_eq_half_parityBox, integral_physicalNearest_parityBox]
  norm_num

/-- The true D4 quantization constant, derived directly from the parity quantizer. -/
theorem normalizedMoment_gramMatrix :
    normalizedMoment (gramMatrix ℝ) = optimalConstant :=
  normalizedMoment_gramMatrix_of_moment moment_gramMatrix

end D4.Quantizer
