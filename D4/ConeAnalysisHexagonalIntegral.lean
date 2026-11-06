import D4.ConeAnalysisHexagonalLattice
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! Direct physical area and second-moment integrals of the hexagonal cell. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace D4.Hexagonal
open Set MeasureTheory

private theorem hs : 0 < Real.sqrt 3 := by positivity

def height (x : ℝ) : ℝ := (1-|x|)/Real.sqrt 3

def planeHexagon : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-(1/2):ℝ) (1/2) ∧ p.2 ∈ Icc (-height p.1) (height p.1)}

theorem height_continuous : Continuous height := (continuous_const.sub continuous_abs).div_const _

theorem planeHexagon_compact : IsCompact planeHexagon := by
  have hc : IsClosed planeHexagon := by
    exact ((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_fst continuous_const)).inter
      ((isClosed_le (height_continuous.comp continuous_fst).neg continuous_snd).inter
        (isClosed_le continuous_snd (height_continuous.comp continuous_fst)))
  have hb : planeHexagon ⊆ (Icc (-1:ℝ) 1) ×ˢ (Icc (-1:ℝ) 1) := by
    intro p hp
    have hx : |p.1| ≤ 1/2 := abs_le.mpr hp.1
    have hh : height p.1 ≤ 1 := by
      have hs1 : 1 ≤ Real.sqrt 3 := (Real.one_le_sqrt).mpr (by norm_num)
      apply (div_le_one hs).mpr
      linarith [abs_nonneg p.1]
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hc hb

theorem planeHexagon_slices (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    (∫ p in planeHexagon, f p ∂((volume : Measure ℝ).prod volume)) =
      ∫ x in Icc (-(1/2):ℝ) (1/2), ∫ y in Icc (-height x) (height x), f (x,y) := by
  have hm := planeHexagon_compact.measurableSet
  have hi : IntegrableOn f planeHexagon ((volume : Measure ℝ).prod volume) :=
    hf.continuousOn.integrableOn_compact planeHexagon_compact
  rw [← integral_indicator hm, integral_prod _ (hi.integrable_indicator hm),
    ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ Icc (-(1/2):ℝ) (1/2)
    · rw [indicator_of_mem hx, ← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        by_cases hy : y ∈ Icc (-height x) (height x)
        · have hp : (x,y) ∈ planeHexagon := ⟨hx,hy⟩
          simp only [indicator_of_mem hp,indicator_of_mem hy]
        · have hp : (x,y) ∉ planeHexagon := fun h => hy h.2
          simp only [indicator_of_not_mem hp,indicator_of_not_mem hy]
    · rw [indicator_of_not_mem hx]
      apply integral_eq_zero_of_ae
      exact Filter.Eventually.of_forall fun y =>
        indicator_of_not_mem (show (x,y) ∉ planeHexagon from fun h => hx h.1) f

def coordinateMeasurableEquiv : (ℝ × ℝ) ≃ᵐ Point :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toHomeomorph.toMeasurableEquiv

theorem coordinate_measurePreserving : MeasurePreserving coordinateMeasurableEquiv
    ((volume : Measure ℝ).prod volume) volume := by
  exact MeasurePreserving.symm
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).toHomeomorph.toMeasurableEquiv
    (D4.ConeAnalysis.prodLp_volume_preserving (E:=ℝ) (F:=ℝ))

theorem hexagon_eq_coordinate_image : hexagon = coordinateMeasurableEquiv '' planeHexagon := by
  ext p
  constructor
  · intro hp
    refine ⟨(p.fst,p.snd), ⟨abs_le.mp hp.1, abs_le.mp hp.2⟩, ?_⟩
    apply (WithLp.equiv 2 (ℝ × ℝ)).injective
    rfl
  · rintro ⟨p,hp,rfl⟩
    exact ⟨abs_le.mpr hp.1,abs_le.mpr hp.2⟩

theorem integral_hexagon (f : Point → ℝ) :
    (∫ p in hexagon, f p) = ∫ p in planeHexagon, f (point p.1 p.2)
      ∂((volume : Measure ℝ).prod volume) := by
  rw [hexagon_eq_coordinate_image]
  exact coordinate_measurePreserving.setIntegral_image_emb
    coordinateMeasurableEquiv.measurableEmbedding f planeHexagon

theorem vertical_area (x : ℝ) (hx : x ∈ Icc (-(1/2):ℝ) (1/2)) :
    (∫ _y in Icc (-height x) (height x), (1:ℝ)) = 2*height x := by
  have hh : 0 ≤ height x := div_nonneg (by have h := abs_le.mpr hx; linarith) hs.le
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -height x ≤ height x),
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem vertical_moment (x : ℝ) (hx : x ∈ Icc (-(1/2):ℝ) (1/2)) :
    (∫ y in Icc (-height x) (height x), x^2+y^2) = 2*x^2*height x+2/3*(height x)^3 := by
  have hh : 0 ≤ height x := div_nonneg (by have h := abs_le.mpr hx; linarith) hs.le
  have h₀ : IntervalIntegrable (fun _y : ℝ => x^2) volume (-height x) (height x) := intervalIntegrable_const
  have h₂ : IntervalIntegrable (fun y : ℝ => y^2) volume (-height x) (height x) :=
    (show Continuous (fun y : ℝ => y^2) from continuous_id.pow 2).intervalIntegrable _ _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -height x ≤ height x),
    intervalIntegral.integral_add h₀ h₂,
    intervalIntegral.integral_const, integral_pow]
  simp only [smul_eq_mul]
  norm_num
  ring


private theorem cubic_integral (a b c₀ c₁ c₂ c₃ : ℝ) :
    (∫ x in a..b, c₀+c₁*x+c₂*x^2+c₃*x^3) =
      c₀*(b-a)+c₁*(b^2-a^2)/2+c₂*(b^3-a^3)/3+c₃*(b^4-a^4)/4 := by
  have h₀ : IntervalIntegrable (fun _ : ℝ => c₀) volume a b := intervalIntegrable_const
  have h₁ : IntervalIntegrable (fun x : ℝ => c₁*x) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable a b
  have h₂ : IntervalIntegrable (fun x : ℝ => c₂*x^2) volume a b :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable a b
  have h₃ : IntervalIntegrable (fun x : ℝ => c₃*x^3) volume a b :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable a b
  rw [intervalIntegral.integral_add ((h₀.add h₁).add h₂) h₃,
    intervalIntegral.integral_add (h₀.add h₁) h₂, intervalIntegral.integral_add h₀ h₁,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id,
    integral_pow, integral_pow]
  simp only [smul_eq_mul]
  norm_num
  ring

private theorem sqrt_three_cube : (Real.sqrt 3)^3 = 3*Real.sqrt 3 := by
  rw [pow_succ, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

theorem height_area_integral :
    (∫ x in Icc (-(1/2):ℝ) (1/2), 2*height x) = Real.sqrt 3/2 := by
  have hc : Continuous (fun x => 2*height x) := continuous_const.mul height_continuous
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hleft : (∫ x in (-(1/2):ℝ)..0, 2*height x) =
      (2/Real.sqrt 3)*(∫ x in (-(1/2):ℝ)..0, (1:ℝ)+1*x+0*x^2+0*x^3) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ≤ 0 := (show x ∈ Icc (-(1/2):ℝ) 0 by simpa only [uIcc_of_le (by norm_num : (-(1/2):ℝ) ≤ 0)] using hx).2
    simp [height, abs_of_nonpos hx']
    ring
  have hright : (∫ x in (0:ℝ)..(1/2), 2*height x) =
      (2/Real.sqrt 3)*(∫ x in (0:ℝ)..(1/2), (1:ℝ)+(-1)*x+0*x^2+0*x^3) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : 0 ≤ x := (show x ∈ Icc (0:ℝ) (1/2) by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] using hx).1
    simp [height, abs_of_nonneg hx']
    ring
  rw [hleft, hright, cubic_integral, cubic_integral]
  norm_num
  field_simp [hs.ne']
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

theorem height_moment_integral :
    (∫ x in Icc (-(1/2):ℝ) (1/2), 2*x^2*height x+2/3*(height x)^3) = 5*Real.sqrt 3/72 := by
  have hc : Continuous (fun x => 2*x^2*height x+2/3*(height x)^3) := by
    exact ((continuous_const.mul (continuous_id.pow 2)).mul height_continuous).add
      (continuous_const.mul (height_continuous.pow 3))
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hleft : (∫ x in (-(1/2):ℝ)..0, 2*x^2*height x+2/3*(height x)^3) =
      (2/Real.sqrt 3)*(∫ x in (-(1/2):ℝ)..0, (1/9:ℝ)+(1/3)*x+(4/3)*x^2+(10/9)*x^3) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ≤ 0 := (show x ∈ Icc (-(1/2):ℝ) 0 by simpa only [uIcc_of_le (by norm_num : (-(1/2):ℝ) ≤ 0)] using hx).2
    simp only [height, abs_of_nonpos hx', sub_neg_eq_add, div_pow, sqrt_three_cube]
    field_simp [hs.ne']
    ring
  have hright : (∫ x in (0:ℝ)..(1/2), 2*x^2*height x+2/3*(height x)^3) =
      (2/Real.sqrt 3)*(∫ x in (0:ℝ)..(1/2), (1/9:ℝ)+(-1/3)*x+(4/3)*x^2+(-10/9)*x^3) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : 0 ≤ x := (show x ∈ Icc (0:ℝ) (1/2) by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] using hx).1
    simp only [height, abs_of_nonneg hx', div_pow, sqrt_three_cube]
    field_simp [hs.ne']
    ring
  rw [hleft, hright, cubic_integral, cubic_integral]
  norm_num
  field_simp [hs.ne']
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]


theorem hexagon_area : volume.real hexagon = Real.sqrt 3/2 := by
  calc
    volume.real hexagon = ∫ _p in hexagon, (1:ℝ) := by simp
    _ = ∫ _p in planeHexagon, (1:ℝ) ∂((volume : Measure ℝ).prod volume) := integral_hexagon _
    _ = ∫ x in Icc (-(1/2):ℝ) (1/2), ∫ _y in Icc (-height x) (height x), (1:ℝ) :=
      planeHexagon_slices _ continuous_const
    _ = ∫ x in Icc (-(1/2):ℝ) (1/2), 2*height x :=
      setIntegral_congr_fun measurableSet_Icc (fun x hx => vertical_area x hx)
    _ = Real.sqrt 3/2 := height_area_integral

theorem hexagon_secondMoment : (∫ p in hexagon, ‖p‖^2) = 5*Real.sqrt 3/72 := by
  calc
    (∫ p in hexagon, ‖p‖^2) =
        ∫ p in planeHexagon, p.1^2+p.2^2 ∂((volume : Measure ℝ).prod volume) := by
      rw [integral_hexagon]
      apply setIntegral_congr_fun planeHexagon_compact.measurableSet
      intro p hp
      simp only [norm_sq, point_fst, point_snd]
    _ = ∫ x in Icc (-(1/2):ℝ) (1/2), ∫ y in Icc (-height x) (height x), x^2+y^2 :=
      planeHexagon_slices _ ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    _ = ∫ x in Icc (-(1/2):ℝ) (1/2), 2*x^2*height x+2/3*(height x)^3 :=
      setIntegral_congr_fun measurableSet_Icc (fun x hx => vertical_moment x hx)
    _ = 5*Real.sqrt 3/72 := height_moment_integral

/-- The actual full-rank triangular lattice attains the sharp two-dimensional bound. -/
theorem normalizedCellMoment_lattice : D4.FacetGeometry.normalizedCellMoment lattice =
    5/(36*Real.sqrt 3) := by
  rw [D4.FacetGeometry.normalizedCellMoment, voronoi_eq_hexagon, dimension_two,
    hexagon_area, hexagon_secondMoment]
  norm_num [D4.ConePerspective.normalizedMoment, Real.rpow_two]
  field_simp [hs.ne']
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

end D4.Hexagonal
