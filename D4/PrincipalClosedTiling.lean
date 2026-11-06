import D4.PrincipalMoment
import Mathlib.Analysis.Convex.Measure

/-! The checked principal tiles cover pointwise and have disjoint interiors.
The almost-everywhere integral tiling is upgraded using closedness. -/
noncomputable section
namespace D4.Principal
open Set MeasureTheory Filter Analytic Matrix

theorem closed_cover_of_convex_ae {S T : Set Vec} (hS : IsClosed S)
    (hT : IsClosed T) (hc : Convex ℝ S) (hi : (interior S).Nonempty)
    (hsub : T⊆S) (hae : T=ᵐ[volume]S) : T=S := by
  classical
  have hn : volume (interior S\T)=0 := by
    have he : ∀ᵐ x ∂(volume : Measure Vec),x∉interior S\T := by
      filter_upwards [hae] with x hx
      intro hh
      exact hh.2 (hx.mpr (interior_subset hh.1))
    simpa only [ae_iff,not_not] using he
  have he : interior S\T=∅ := (isOpen_interior.inter hT.isOpen_compl).eq_empty_of_measure_zero hn
  have his : interior S⊆T := by
    intro x hx
    by_contra hnot
    have hm : x∈interior S\T := ⟨hx,hnot⟩
    rw [he] at hm
    exact hm
  apply Set.Subset.antisymm hsub
  rw [← hS.closure_eq,← hc.closure_interior_eq_closure_of_nonempty_interior hi]
  exact closure_minimal his hT

theorem treeTiles_cover (w : Fin 10 → ℝ) (hw : ∀ e,0<w e) :
    (⋃ t : Fin 125,treeTile w t)=zonotope w := by
  apply closed_cover_of_convex_ae (zonotope_isCompact w).isClosed
    (isCompact_iUnion (fun t => upperTile_compact realTreeHeight w (realTreeNormal t))).isClosed
    (zonotope_convex w)
  · apply (isOpen_interior.measure_pos_iff volume).mp
    rw [measure_interior_of_null_frontier ((zonotope_convex w).addHaar_frontier volume),
      zonotope_volume (fun e => (hw e).le) (principal_posDef_of_pos hw)]
    exact ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) (principal_posDef_of_pos hw).det_pos)
  · exact iUnion_subset (fun t => upperTile_subset_zonotope realTreeHeight w (realTreeNormal t))
  · exact upperTiles_ae_cover realTreeHeight w realTreeNormal realTreeNormal_injective
      (treeTile_volume_sum w hw)

theorem treeTiles_disjoint_interiors (w : Fin 10 → ℝ) (s t : Fin 125) (hst : s≠t) :
    Disjoint (interior (treeTile w s)) (interior (treeTile w t)) := by
  apply disjoint_iff_inter_eq_empty.mpr
  apply (isOpen_interior.inter isOpen_interior).eq_empty_of_measure_zero (μ := volume)
  exact measure_mono_null (inter_subset_inter interior_subset interior_subset)
    (upperTile_inter_volume realTreeHeight w (realTreeNormal_injective.ne hst))

/-- Every point of the zonotope has a lift on one of the checked upper
facets, and this lift maximizes the actual lifting height in its fiber. -/
theorem tree_lift_maximizes_height (w : Fin 10 → ℝ) (hw : ∀ e,0<w e)
    (r : Vec) (hr : r∈zonotope w) :
    ∃ T : Fin 125,∃ t : Fin 10 → ℝ,
      t∈upperFace realTreeHeight w (realTreeNormal T) ∧ generatorMap t=r ∧
      ∀ s∈Icc (-w) w,generatorMap s=r → dotProduct realTreeHeight s≤dotProduct realTreeHeight t := by
  rw [← treeTiles_cover w hw] at hr
  obtain ⟨T,t,ht,htr⟩ := mem_iUnion.mp hr
  refine ⟨T,t,ht,htr,?_⟩
  intro s hs hsr
  have hb := upper_height_bound realTreeHeight w (realTreeNormal T) hs
  rw [hsr,← htr,← upper_height_eq realTreeHeight w (realTreeNormal T) ht] at hb
  exact hb

end D4.Principal
