import D4.ConeAnalysisConvexBase

/-! Concrete boundary rays certify nonconstancy of the actual Minkowski
radial function; no nonconstancy hypothesis is hidden in the construction. -/
noncomputable section
namespace D4.ConeAnalysis
open Set Metric
open scoped Pointwise

 theorem gauge_eq_one_of_radial_endpoint {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E} {x : E}
    (hB : Absorbent ℝ B) (hx : x∈B) (hout : ∀ s : ℝ,1<s → s • x∉B) :
    gauge B x=1 := by
  apply le_antisymm (gauge_le_one_of_mem hx)
  by_contra h
  obtain ⟨r,hr,hr1,hrx⟩ := exists_lt_of_gauge_lt hB (lt_of_not_ge h)
  have hm : r⁻¹ • x∈B := (mem_smul_set_iff_inv_smul_mem₀ hr.ne' B x).mp hrx
  exact hout r⁻¹ ((one_lt_inv₀ hr).mpr hr1) hm

 theorem gaugeRadius_nonconstant_of_endpoints {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E} {x y : E}
    (hx : gauge B x=1) (hy : gauge B y=1) (hne : ‖x‖≠‖y‖) :
    ∃ u v : sphere (0:E) 1,gaugeRadius B u≠gaugeRadius B v := by
  have hx0 : x≠0 := by intro h; simpa [h] using hx
  have hy0 : y≠0 := by intro h; simpa [h] using hy
  have hxpos : 0<‖x‖ := norm_pos_iff.mpr hx0
  have hypos : 0<‖y‖ := norm_pos_iff.mpr hy0
  have hunit (z : E) (hz : 0<‖z‖) : ‖z‖⁻¹ • z∈sphere (0:E) 1 := by
    rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hz),inv_mul_cancel₀ hz.ne']
  refine ⟨⟨‖x‖⁻¹ • x,hunit x hxpos⟩,⟨‖y‖⁻¹ • y,hunit y hypos⟩,?_⟩
  simpa only [gaugeRadius,gauge_smul_of_nonneg (inv_nonneg.mpr hxpos.le),
    gauge_smul_of_nonneg (inv_nonneg.mpr hypos.le),smul_eq_mul,hx,hy,mul_one,inv_inv] using hne

end D4.ConeAnalysis
