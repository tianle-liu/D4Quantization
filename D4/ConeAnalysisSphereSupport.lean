import D4.ConeAnalysisSphereMeasure

/-! The actual uniform sphere measure has full topological support. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped Pointwise

instance toSphere_isOpenPosMeasure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] :
    IsOpenPosMeasure μ.toSphere := by
  constructor
  intro U hU hn
  let r : Ioi (0:ℝ) := ⟨1, by norm_num⟩
  let S := homeomorphUnitSphereProd E ⁻¹' (U ×ˢ Iio r)
  have hs : IsOpen S := (hU.prod isOpen_Iio).preimage (homeomorphUnitSphereProd E).continuous
  have ho : IsOpen (Subtype.val '' S : Set E) := isOpen_compl_singleton.isOpenMap_subtype_val S hs
  have hne : (Subtype.val '' S : Set E).Nonempty := by
    obtain ⟨u, hu⟩ := hn
    let q : sphere (0:E) 1 × Ioi (0:ℝ) := (u, ⟨1/2, by norm_num⟩)
    refine ⟨((homeomorphUnitSphereProd E).symm q).1, ?_⟩
    refine ⟨(homeomorphUnitSphereProd E).symm q, ?_, rfl⟩
    change homeomorphUnitSphereProd E ((homeomorphUnitSphereProd E).symm q) ∈ U ×ˢ Iio r
    rw [Homeomorph.apply_symm_apply]
    exact ⟨hu, by norm_num [q, r]⟩
  have hp : μ (Ioo (0:ℝ) 1 • (Subtype.val '' U)) ≠ 0 := by
    rw [← toSphere_apply_aux μ U r]
    exact ho.measure_ne_zero μ hne
  rw [toSphere_apply' μ hU.measurableSet]
  exact mul_ne_zero (by exact_mod_cast (Module.finrank_pos (R:=ℝ) (M:=E)).ne') hp

instance uniformSphere_isOpenPosMeasure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] :
    IsOpenPosMeasure (uniformSphere μ) := by
  constructor
  intro U hU hn
  rw [uniformSphere, Measure.smul_apply, smul_eq_mul]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (hU.measure_ne_zero μ.toSphere hn)

end D4.ConeAnalysis
