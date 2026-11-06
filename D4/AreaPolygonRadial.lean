import D4.AreaTriangleHull
import Mathlib.Analysis.Convex.Gauge

/-! Coverage of a convex polygon by triangles follows from its actual
boundary edges, rather than being an extra triangulation hypothesis. -/
noncomputable section
namespace D4.AreaEnvelope
open Set Matrix
open scoped Topology

theorem mem_segment_zero_frontier {K : Set Plane} (hK : IsCompact K)
    (hc : Convex ℝ K) (h0 : (0:Plane) ∈ interior K) {x : Plane} (hx : x ∈ K)
    (hxn : x≠0) : ∃ y ∈ frontier K, x ∈ segment ℝ 0 y := by
  have hn : K ∈ nhds (0:Plane) := mem_interior_iff_mem_nhds.mp h0
  have hg : 0 < gauge K x :=
    (gauge_pos (absorbent_nhds_zero hn)
      (NormedSpace.isVonNBounded_of_isBounded ℝ hK.isBounded)).mpr hxn
  have hle : gauge K x ≤ 1 := gauge_le_one_of_mem hx
  let y := (gauge K x)⁻¹ • x
  have hy : y ∈ frontier K := by
    apply (gauge_eq_one_iff_mem_frontier hc hn).mp
    dsimp [y]
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hg.le),smul_eq_mul,inv_mul_cancel₀ hg.ne']
  refine ⟨y,hy,?_⟩
  rw [segment_eq_image]
  refine ⟨gauge K x,⟨hg.le,hle⟩,?_⟩
  simp only [smul_zero,zero_add,y,smul_smul,mul_inv_cancel₀ hg.ne',one_smul]

theorem polygon_fan_cover {ι : Type*} [Nonempty ι]
    (K : Set Plane) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0:Plane) ∈ interior K) (a b : ι → Plane)
    (hedges : frontier K=⋃ i,segment ℝ (a i) (b i)) :
    (⋃ i,affineTriangle (triangleMatrix (a i) (b i)) 0)=K := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    rw [affineTriangle_eq_convexHull] at hi
    apply convexHull_min ?_ hc hi
    intro y hy
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact interior_subset h0
    · apply hK.isClosed.frontier_subset
      rw [hedges]
      exact Set.mem_iUnion.mpr ⟨i,left_mem_segment ℝ _ _⟩
    · apply hK.isClosed.frontier_subset
      rw [hedges]
      exact Set.mem_iUnion.mpr ⟨i,right_mem_segment ℝ _ _⟩
  · intro x hx
    by_cases hxn : x=0
    · subst x
      obtain ⟨i⟩ := ‹Nonempty ι›
      exact Set.mem_iUnion.mpr ⟨i,affineTriangle_vertices (a i) (b i) 0⟩
    obtain ⟨y,hy,hxy⟩ := mem_segment_zero_frontier hK hc h0 hx hxn
    rw [hedges] at hy
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨i,?_⟩
    rw [affineTriangle_eq_convexHull]
    exact (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (by simp))
      (segment_subset_convexHull (by simp) (by simp) hi) hxy

end D4.AreaEnvelope
