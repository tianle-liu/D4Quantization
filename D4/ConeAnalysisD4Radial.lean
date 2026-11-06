import D4.ConeAnalysisD4Octahedron
import D4.ConeAnalysisGaugeNonconstant
import D4.ConeAnalysisFacet

/-! Nonconstancy of the actual radial function of every D4 octahedral facet. -/
noncomputable section
namespace D4.PhysicalD4
open Set Metric Euclidean Analytic FacetGeometry ConeAnalysis
open scoped InnerProductSpace Pointwise

 theorem octahedronChart_smul (s : ℝ) (a : Fin 3 → ℝ) :
    octahedronChart (s • a)=s • octahedronChart a := by
  ext i
  fin_cases i <;> simp [octahedronChart] <;> ring

 theorem octahedronChart_tangent (a : Fin 3 → ℝ) :
    octahedronChart a∈tangent standardRoot := by
  rw [mem_tangent,real_inner_comm,standardRoot,integerPoint_inner]
  norm_num [octahedronChart,Fin.sum_univ_succ]
  ring

 def tangentOctahedronChart (a : Fin 3 → ℝ) : tangent standardRoot :=
  ⟨octahedronChart a,octahedronChart_tangent a⟩

 theorem tangentOctahedronChart_mem_base (a : Fin 3 → ℝ) :
    tangentOctahedronChart a∈base lattice standardRoot ↔ |a 0|+|a 1|+|a 2|≤1 := by
  rw [← standard_face_chart]
  exact ⟨base_point_mem_face,fun h => h.1⟩

 theorem tangentOctahedronChart_smul (s : ℝ) (a : Fin 3 → ℝ) :
    tangentOctahedronChart (s • a)=s • tangentOctahedronChart a :=
  Subtype.ext (octahedronChart_smul s a)

 theorem standard_base_gauge_chart (a : Fin 3 → ℝ) (ha : |a 0|+|a 1|+|a 2|=1) :
    gauge (base lattice standardRoot) (tangentOctahedronChart a)=1 := by
  apply gauge_eq_one_of_radial_endpoint
    (absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp (facet_center_interior standardRoot_isFacet)))
    ((tangentOctahedronChart_mem_base a).mpr ha.le)
  intro s hs hm
  rw [← tangentOctahedronChart_smul,tangentOctahedronChart_mem_base] at hm
  simp only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (by linarith : 0<s)] at hm
  have he : s*|a 0|+s*|a 1|+s*|a 2|=s := by rw [← mul_add,← mul_add,ha,mul_one]
  linarith

 theorem standard_base_radial_nonconstant :
    ∃ u v : sphere (0:tangent standardRoot) 1,
      gaugeRadius (base lattice standardRoot) u≠gaugeRadius (base lattice standardRoot) v := by
  apply gaugeRadius_nonconstant_of_endpoints
    (standard_base_gauge_chart ![1,0,0] (by change |(1:ℝ)|+|0|+|0|=1; norm_num))
    (standard_base_gauge_chart ![1/2,1/2,0] (by change |(1/2:ℝ)|+|1/2|+|0|=1; rw [abs_of_pos (by norm_num : (0:ℝ)<1/2)]; norm_num))
  intro h
  have hh := congrArg (fun r : ℝ => r^2) h
  change ‖octahedronChart ![1,0,0]‖^2=‖octahedronChart ![1/2,1/2,0]‖^2 at hh
  rw [octahedronChart_norm_sq,octahedronChart_norm_sq] at hh
  change ((1:ℝ)^2+0^2+0^2)/2=((1/2)^2+(1/2)^2+0^2)/2 at hh
  norm_num at hh

 theorem face_center_dist_sq {L : Submodule ℤ Point} {z x : Point}
    (hx : x∈face L z) : ‖x-(1/2:ℝ) • z‖^2=‖x‖^2-‖z‖^2/4 := by
  rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,real_inner_smul_right]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  nlinarith [hx.2]

 theorem facet_isometry_normal {z : Point} (hz : IsFacetVector lattice z)
    (e : Point ≃ₗᵢ[ℝ] Point) (he : e '' face lattice standardRoot=face lattice z) :
    e standardRoot=z := by
  have hs : (1/2:ℝ) • standardRoot∈face lattice standardRoot := by
    simpa using base_point_mem_face (interior_subset (facet_center_interior standardRoot_isFacet))
  have ht : (1/2:ℝ) • z∈face lattice z := by
    simpa using base_point_mem_face (interior_subset (facet_center_interior hz))
  have hm : e ((1/2:ℝ) • standardRoot)∈face lattice z := by rw [← he]; exact mem_image_of_mem _ hs
  obtain ⟨y,hy,hye⟩ := (he.symm ▸ ht)
  have h1 := face_center_dist_sq hm
  have h2 := face_center_dist_sq hy
  have hnorm : ‖y‖=‖(1/2:ℝ) • z‖ := by rw [← hye,e.norm_map]
  rw [e.norm_map] at h1
  rw [hnorm] at h2
  simp only [norm_smul,Real.norm_eq_abs,show |(1/2:ℝ)|=1/2 by norm_num] at h1 h2
  have hn : ‖e ((1/2:ℝ) • standardRoot)-(1/2:ℝ) • z‖=0 := by
    nlinarith [sq_nonneg ‖y-(1/2:ℝ) • standardRoot‖,
      norm_nonneg (e ((1/2:ℝ) • standardRoot)-(1/2:ℝ) • z)]
  have hhalf := sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hh := congrArg (fun x : Point => (2:ℝ) • x) hhalf
  simpa only [map_smul,smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul] using hh

 theorem facet_base_transport {z : Point} (hz : IsFacetVector lattice z)
    (e : Point ≃ₗᵢ[ℝ] Point) (he : e '' face lattice standardRoot=face lattice z)
    (a : Fin 3 → ℝ) :
    ∃ x : tangent z, (x:Point)=e (octahedronChart a) ∧
      (x∈base lattice z ↔ |a 0|+|a 1|+|a 2|≤1) := by
  have hez := facet_isometry_normal hz e he
  have hm : e (octahedronChart a)∈tangent z := by
    rw [mem_tangent,← hez,e.inner_map_map]
    exact octahedronChart_tangent a
  refine ⟨⟨e (octahedronChart a),hm⟩,rfl,?_⟩
  have hmap : (1/2:ℝ) • z+e (octahedronChart a)=
      e ((1/2:ℝ) • standardRoot+octahedronChart a) := by rw [map_add,map_smul,hez]
  constructor
  · intro hx
    have hh := base_point_mem_face hx
    change (1/2:ℝ) • z+e (octahedronChart a)∈face lattice z at hh
    rw [hmap,← he] at hh
    obtain ⟨y,hy,hyx⟩ := hh
    exact (standard_face_chart a).mp (e.injective hyx ▸ hy)
  · intro ha
    have hh := mem_image_of_mem e ((standard_face_chart a).mpr ha)
    rw [he,← hmap] at hh
    exact hh.1

theorem facet_gauge_chart {z : Point} (hz : IsFacetVector lattice z)
    (e : Point ≃ₗᵢ[ℝ] Point) (he : e '' face lattice standardRoot=face lattice z)
    (a : Fin 3 → ℝ) (ha : |a 0|+|a 1|+|a 2|=1) :
    ∃ x : tangent z, (x:Point)=e (octahedronChart a) ∧ gauge (base lattice z) x=1 := by
  obtain ⟨x,hx,hm⟩ := facet_base_transport hz e he a
  refine ⟨x,hx,gauge_eq_one_of_radial_endpoint
    (absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp (facet_center_interior hz)))
    (hm.mpr ha.le) ?_⟩
  intro s hs hmem
  obtain ⟨y,hy,hm'⟩ := facet_base_transport hz e he (s • a)
  have hyx : y=s • x := by
    apply Subtype.ext
    change (y:Point)=s • (x:Point)
    rw [hy,hx,octahedronChart_smul,map_smul]
  rw [← hyx] at hmem
  have hh := hm'.mp hmem
  simp only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (by linarith : 0<s)] at hh
  have hs' : s*|a 0|+s*|a 1|+s*|a 2|=s := by rw [← mul_add,← mul_add,ha,mul_one]
  linarith

/-- The radial function of every actual D4 facet is nonconstant. -/
theorem facet_base_radial_nonconstant {z : Point} (hz : IsFacetVector lattice z) :
    ∃ u v : sphere (0:tangent z) 1,
      gaugeRadius (base lattice z) u≠gaugeRadius (base lattice z) v := by
  obtain ⟨e,he'⟩ := facet_isometric_octahedron hz
  have he : e '' face lattice standardRoot=face lattice z := by
    rw [standard_face_eq_octahedron]
    exact he'.symm
  obtain ⟨x,hx,hgx⟩ := facet_gauge_chart hz e he ![1,0,0]
    (by change |(1:ℝ)|+|0|+|0|=1; norm_num)
  obtain ⟨y,hy,hgy⟩ := facet_gauge_chart hz e he ![1/2,1/2,0]
    (by change |(1/2:ℝ)|+|1/2|+|0|=1; rw [abs_of_pos (by norm_num : (0:ℝ)<1/2)]; norm_num)
  apply gaugeRadius_nonconstant_of_endpoints hgx hgy
  intro h
  have hh := congrArg (fun r : ℝ => r^2) h
  change ‖(x:Point)‖^2=‖(y:Point)‖^2 at hh
  rw [hx,hy,e.norm_map,e.norm_map,octahedronChart_norm_sq,octahedronChart_norm_sq] at hh
  change ((1:ℝ)^2+0^2+0^2)/2=((1/2)^2+(1/2)^2+0^2)/2 at hh
  norm_num at hh

/-- Height normalization preserves the strict radial variation of the octahedron. -/
theorem normalized_facet_base_radial_nonconstant {z : Point} (hz : IsFacetVector lattice z) :
    ∃ u v : sphere (0:tangent z) 1,
      gaugeRadius (normalizedFacetBase lattice z) u≠
        gaugeRadius (normalizedFacetBase lattice z) v := by
  obtain ⟨u,v,hne⟩ := facet_base_radial_nonconstant hz
  refine ⟨u,v,?_⟩
  have hheight := facetHeight_pos hz.2.1
  have hscale (w : sphere (0:tangent z) 1) :
      gaugeRadius (normalizedFacetBase lattice z) w=
        (facetHeight z)⁻¹*gaugeRadius (base lattice z) w := by
    simp only [gaugeRadius,normalizedFacetBase,
      gauge_smul_left_of_nonneg (inv_nonneg.mpr hheight.le),
      Pi.smul_apply,smul_eq_mul,inv_inv,mul_inv_rev]
    ring
  rw [hscale,hscale]
  exact fun h => hne (mul_left_cancel₀ (inv_ne_zero hheight.ne') h)

end D4.PhysicalD4
