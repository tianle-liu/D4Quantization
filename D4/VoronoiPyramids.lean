import D4.VoronoiPolyhedron
import Mathlib.Analysis.Convex.Gauge
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Actual radial pyramids over the faces of the lattice Voronoi cell. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace Topology
namespace D4.FacetGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : Submodule ℤ E}

/-- The radial pyramid with the apex and base omitted. Lateral faces are retained. -/
def pyramid (L : Submodule ℤ E) (z : E) : Set E :=
  {x | ∃ t ∈ Ioo (0:ℝ) 1, ∃ y ∈ face L z, x = t • y}

def closedPyramid (L : Submodule ℤ E) (z : E) : Set E :=
  {x | ∃ t ∈ Icc (0:ℝ) 1, ∃ y ∈ face L z, x = t • y}

theorem face_eq_base_image (L : Submodule ℤ E) (z : E) :
    face L z = (fun y : tangent z => (1/2:ℝ) • z + (y:E)) '' base L z := by
  ext x
  constructor
  · intro hx
    have ht : x-(1/2:ℝ) • z ∈ tangent z := by
      rw [mem_tangent, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
        real_inner_comm]
      linarith [hx.2]
    refine ⟨⟨x-(1/2:ℝ) • z, ht⟩, ?_, ?_⟩
    · change (1/2:ℝ) • z + (x-(1/2:ℝ) • z) ∈ voronoi L
      convert hx.1 using 1 <;> abel
    · simp
  · rintro ⟨y, hy, rfl⟩
    exact base_point_mem_face hy

theorem pyramid_eq_base_image (L : Submodule ℤ E) (z : E) :
    pyramid L z = {x | ∃ t ∈ Ioo (0:ℝ) 1, ∃ y ∈ base L z,
      x = t • ((1/2:ℝ) • z + (y:E))} := by
  ext x
  simp only [pyramid, face_eq_base_image, mem_setOf_eq, mem_image]
  constructor
  · rintro ⟨t, ht, _, ⟨y, hy, rfl⟩, he⟩
    exact ⟨t, ht, y, hy, he⟩
  · rintro ⟨t, ht, y, hy, he⟩
    exact ⟨t, ht, _, ⟨y, hy, rfl⟩, he⟩

theorem pyramid_subset_closedPyramid (L : Submodule ℤ E) (z : E) :
    pyramid L z ⊆ closedPyramid L z := by
  rintro x ⟨t, ht, y, hy, he⟩
  exact ⟨t, ⟨ht.1.le, ht.2.le⟩, y, hy, he⟩

theorem closedPyramid_subset_voronoi (L : Submodule ℤ E) (z : E) :
    closedPyramid L z ⊆ voronoi L := by
  rintro x ⟨t, ht, y, hy, rfl⟩
  have h0 : (0:E) ∈ voronoi L := by intro z hz; simp
  have h := voronoi_convex L h0 hy.1 (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  simpa using h

variable [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]

theorem face_compact (z : E) : IsCompact (face L z) :=
  (voronoi_compact_full (L := L)).inter_right
    (isClosed_eq (continuous_const.mul (continuous_id.inner continuous_const)) continuous_const)

theorem closedPyramid_compact (z : E) : IsCompact (closedPyramid L z) := by
  have he : closedPyramid L z = (fun p : ℝ × E => p.1 • p.2) ''
      ((Icc (0:ℝ) 1) ×ˢ face L z) := by
    ext x
    simp only [closedPyramid, mem_setOf_eq, mem_image, mem_prod, Prod.exists]
    constructor
    · rintro ⟨t, ht, y, hy, he⟩
      exact ⟨t, y, ⟨ht, hy⟩, he.symm⟩
    · rintro ⟨t, y, ⟨ht, hy⟩, he⟩
      exact ⟨t, ht, y, hy, he.symm⟩
  rw [he]
  exact (isCompact_Icc.prod (face_compact z)).image (continuous_fst.smul continuous_snd)

theorem voronoi_radial_frontier {x : E} (hx : x ∈ voronoi L) (hx0 : x ≠ 0) :
    ∃ t ∈ Ioc (0:ℝ) 1, ∃ y ∈ frontier (voronoi L), x = t • y := by
  have hn : voronoi L ∈ 𝓝 (0:E) := mem_interior_iff_mem_nhds.mp zero_mem_interior_voronoi
  have hp : 0 < gauge (voronoi L) x := (gauge_pos (absorbent_nhds_zero hn)
    (NormedSpace.isVonNBounded_of_isBounded ℝ (voronoi_compact_full (L:=L)).isBounded)).mpr hx0
  refine ⟨gauge (voronoi L) x, ⟨hp, gauge_le_one_of_mem hx⟩,
    (gauge (voronoi L) x)⁻¹ • x, ?_, ?_⟩
  · apply (gauge_eq_one_iff_mem_frontier (voronoi_convex L) hn).mp
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hp.le), smul_eq_mul, inv_mul_cancel₀ hp.ne']
  · simp [smul_smul, hp.ne']

theorem voronoi_finite_pyramid_cover {T : Finset E}
    (hT : ∀ x : E, x ∈ voronoi L ↔ ∀ z ∈ T, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2) :
    voronoi L ⊆ {0} ∪ ⋃ z ∈ T, closedPyramid L z := by
  intro x hx
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · obtain ⟨t, ht, y, hy, he⟩ := voronoi_radial_frontier hx hx0
    obtain ⟨z, hz, hyz⟩ := frontier_has_active_vector hT hy
    exact Or.inr (mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, t, ⟨ht.1.le, ht.2⟩, y, hyz, he⟩⟩)

end D4.FacetGeometry
