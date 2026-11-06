import D4.NearestTorus
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Compact subsets with no lattice identifications admit a common open
neighborhood with the same property. -/
noncomputable section
namespace D4.Analytic
open Matrix Set Metric Topology

theorem castVec_isClosedEmbedding : IsClosedEmbedding castVec := by
  apply isClosedEmbedding_of_pairwise_le_dist zero_lt_one
  intro z w hzw
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hzw
  have hh : (1:ℝ) ≤ dist (castVec z i) (castVec w i) :=
    Int.pairwise_one_le_dist hi
  exact hh.trans (dist_le_pi_dist _ _ i)

theorem nonzero_integer_points_closed :
    IsClosed (castVec '' ({0}ᶜ : Set IntVec)) :=
  castVec_isClosedEmbedding.isClosedMap _ (isClosed_discrete _)

theorem compact_integer_embedded_neighborhood (F : Set Vec) (hF : IsCompact F)
    (hinj : ∀ x ∈ F, ∀ n : IntVec, x+castVec n ∈ F → n=0) :
    ∃ U : Set Vec, IsOpen U ∧ F ⊆ U ∧
      ∀ x ∈ U, ∀ n : IntVec, x+castVec n ∈ U → n=0 := by
  classical
  let D : Set Vec := (fun p : Vec × Vec => p.2-p.1) '' (F ×ˢ F)
  have hD : IsCompact D := (hF.prod hF).image (by fun_prop)
  have hd : Disjoint D (castVec '' ({0}ᶜ : Set IntVec)) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩ ⟨n,hn,he⟩
    have hxn : x+castVec n ∈ F := by
      have hh : x+castVec n=y := by rw [he]; dsimp; abel
      rwa [hh]
    exact hn (by simp [hinj x hx n hxn])
  obtain ⟨r,hr,hsep⟩ := EMetric.exists_pos_forall_lt_edist hD nonzero_integer_points_closed hd
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hdist (x y : Vec) (hx : x ∈ F) (hy : y ∈ F) (n : IntVec) (hn : n≠0) :
      (r:ℝ) < ‖y-x-castVec n‖ := by
    have hh := hsep (y-x) ⟨(x,y),⟨hx,hy⟩,rfl⟩ (castVec n) ⟨n,by simpa,rfl⟩
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at hh
    have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (NNReal.coe_nonneg r)).mp hh
    simpa only [dist_eq_norm] using this
  let U : Set Vec := ⋃ x ∈ F, Metric.ball x ((r:ℝ)/3)
  have hU : IsOpen U := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hFU : F ⊆ U := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hx,by simpa using (show 0<(r:ℝ)/3 by positivity)⟩⟩
  refine ⟨U,hU,hFU,?_⟩
  intro x hx n hxn
  by_contra hn
  obtain ⟨f,hf,hxf⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨g,hg,hxng⟩ := Set.mem_iUnion₂.mp hxn
  have hxf' : ‖x-f‖ < (r:ℝ)/3 := hxf
  have hxng' : ‖g-(x+castVec n)‖ < (r:ℝ)/3 := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hxng
  have he : g-f-castVec n=(g-(x+castVec n))+(x-f) := by abel
  have hb := norm_add_le (g-(x+castVec n)) (x-f)
  rw [← he] at hb
  have hlow := hdist f g hf hg n hn
  linarith

end D4.Analytic
