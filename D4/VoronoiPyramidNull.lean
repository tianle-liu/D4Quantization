import D4.VoronoiPyramids
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace Topology
namespace D4.FacetGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : Submodule ℤ E}

theorem face_normal_distinct {z w : E} (hz : z ≠ 0) (hw : w ≠ 0) (hne : z ≠ w) :
    ‖w‖^2 • z - ‖z‖^2 • w ≠ 0 := by
  intro he
  have hs := sub_eq_zero.mp he
  have hn := congrArg norm hs
  simp only [norm_smul, Real.norm_eq_abs, abs_sq] at hn
  have hp : ‖z‖*‖w‖ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hw)
  have hn' : ‖w‖ = ‖z‖ := mul_right_cancel₀ hp (by nlinarith [hn])
  rw [hn'] at hs
  have hc := congrArg (fun x : E => (‖z‖^2)⁻¹ • x) hs
  simp only [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)), one_smul] at hc
  exact hne hc

theorem pyramid_inter_subset_tangent {z w : E} (hz : z ∈ L) (hw : w ∈ L)
    (hz0 : z ≠ 0) (hw0 : w ≠ 0) :
    closedPyramid L z ∩ closedPyramid L w ⊆ (tangent (‖w‖^2 • z-‖z‖^2 • w) : Set E) := by
  rintro x ⟨⟨t, ht, y, hy, he⟩, ⟨s, hs, v, hv, he'⟩⟩
  have hxz : 2*⟪x,z⟫_ℝ = t*‖z‖^2 := by
    rw [he, real_inner_smul_left]
    calc 2*(t*⟪y,z⟫_ℝ) = t*(2*⟪y,z⟫_ℝ) := by ring
         _ = t*‖z‖^2 := by rw [hy.2]
  have hxw : 2*⟪x,w⟫_ℝ = s*‖w‖^2 := by
    rw [he', real_inner_smul_left]
    calc 2*(s*⟪v,w⟫_ℝ) = s*(2*⟪v,w⟫_ℝ) := by ring
         _ = s*‖w‖^2 := by rw [hv.2]
  have htz : t*‖z‖^2 ≤ s*‖z‖^2 := by
    rw [← hxz, he', real_inner_smul_left]
    nlinarith [mul_le_mul_of_nonneg_left ((mem_voronoi_iff L v).mp hv.1 z hz) hs.1]
  have hsw : s*‖w‖^2 ≤ t*‖w‖^2 := by
    rw [← hxw, he, real_inner_smul_left]
    nlinarith [mul_le_mul_of_nonneg_left ((mem_voronoi_iff L y).mp hy.1 w hw) ht.1]
  have heq : t = s := le_antisymm ((mul_le_mul_right (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hz0))).mp htz)
    ((mul_le_mul_right (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw0))).mp hsw)
  change ⟪‖w‖^2 • z-‖z‖^2 • w,x⟫_ℝ = 0
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_comm x z, real_inner_comm x w]
  rw [heq] at hxz
  linear_combination (‖w‖^2/2)*hxz - (‖z‖^2/2)*hxw

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem tangent_volume_zero {z : E} (hz : z ≠ 0) : volume (tangent z : Set E) = 0 := by
  apply Measure.addHaar_submodule volume (tangent z)
  intro he
  have hzmem : z ∈ tangent z := by rw [he]; trivial
  have h := (mem_tangent z z).mp hzmem
  rw [real_inner_self_eq_norm_sq] at h
  exact (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hz)).ne' h

theorem closedPyramid_inter_volume_zero {z w : E} (hz : z ∈ L) (hw : w ∈ L)
    (hz0 : z ≠ 0) (hw0 : w ≠ 0) (hne : z ≠ w) :
    volume (closedPyramid L z ∩ closedPyramid L w) = 0 :=
  measure_mono_null (pyramid_inter_subset_tangent hz hw hz0 hw0)
    (tangent_volume_zero (face_normal_distinct hz0 hw0 hne))


def innerHyperplane (z : E) (c : ℝ) : AffineSubspace ℝ E where
  carrier := {x | ⟪z,x⟫_ℝ = c}
  smul_vsub_vadd_mem a x y w hx hy hw := by
    change ⟪z,a • (x-y)+w⟫_ℝ = c
    rw [inner_add_right, real_inner_smul_right, inner_sub_right, hx, hy, hw]
    ring

theorem innerHyperplane_volume_zero {z : E} (hz : z ≠ 0) (c : ℝ) :
    volume (innerHyperplane z c : Set E) = 0 := by
  apply Measure.addHaar_affineSubspace volume
  intro he
  have h0 : ⟪z,(0:E)⟫_ℝ = c := by
    have hm : (0:E) ∈ innerHyperplane z c := by rw [he]; trivial
    exact hm
  have hz' : ⟪z,z⟫_ℝ = c := by
    have hm : z ∈ innerHyperplane z c := by rw [he]; trivial
    exact hm
  simp only [inner_zero_right] at h0
  rw [real_inner_self_eq_norm_sq, ← h0] at hz'
  exact (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hz)).ne' hz'

theorem face_volume_zero {z : E} (hz : z ≠ 0) : volume (face L z) = 0 := by
  apply measure_mono_null (t := (innerHyperplane z (‖z‖^2/2):Set E))
  · intro x hx
    change ⟪z,x⟫_ℝ = ‖z‖^2/2
    rw [real_inner_comm]
    linarith [hx.2]
  · exact innerHyperplane_volume_zero hz _

theorem closedPyramid_diff_pyramid_subset (z : E) :
    closedPyramid L z \ pyramid L z ⊆ {0} ∪ face L z := by
  rintro x ⟨⟨t, ht, y, hy, he⟩, hn⟩
  by_cases ht0 : t = 0
  · left
    simp [he, ht0]
  by_cases ht1 : t = 1
  · right
    simpa [he, ht1] using hy
  have hti : t ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  exact (hn ⟨t, hti, y, hy, he⟩).elim

theorem closedPyramid_ae_eq_pyramid {z : E} (hz : z ≠ 0) :
    closedPyramid L z =ᵐ[volume] pyramid L z := by
  letI : Nontrivial E := ⟨⟨z, 0, hz⟩⟩
  apply ae_eq_set.mpr
  constructor
  · apply measure_mono_null (closedPyramid_diff_pyramid_subset z)
    exact measure_union_null (measure_singleton 0) (face_volume_zero hz)
  · have he : pyramid L z \ closedPyramid L z = ∅ :=
      diff_eq_empty.mpr (pyramid_subset_closedPyramid L z)
    rw [he, measure_empty]

end D4.FacetGeometry
