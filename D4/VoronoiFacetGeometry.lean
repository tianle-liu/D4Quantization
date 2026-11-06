import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Tactic

/-!
Voronoi face geometry in arbitrary dimension. A facet is a bisector face
with nonempty interior in its supporting hyperplane. The face and the
hyperplane are actual subsets of Euclidean space, defined by all lattice
competitors.
-/
noncomputable section
open Set
open scoped InnerProductSpace

namespace D4.FacetGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def voronoi (L : Submodule ℤ E) : Set E := {x | ∀ z ∈ L, ‖x‖ ≤ ‖x-z‖}

theorem norm_le_sub_iff (x z : E) : ‖x‖ ≤ ‖x-z‖ ↔ 2*⟪x,z⟫_ℝ ≤ ‖z‖^2 := by
  rw [← sq_le_sq₀ (norm_nonneg x) (norm_nonneg (x-z)), norm_sub_sq_real]
  constructor <;> intro h <;> linarith

theorem mem_voronoi_iff (L : Submodule ℤ E) (x : E) :
    x ∈ voronoi L ↔ ∀ z ∈ L, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2 := by
  simp only [voronoi, mem_setOf_eq, norm_le_sub_iff]

theorem voronoi_convex (L : Submodule ℤ E) : Convex ℝ (voronoi L) := by
  intro x hx y hy a b ha hb hab
  rw [mem_voronoi_iff] at hx hy ⊢
  intro z hz
  simp only [inner_add_left, real_inner_smul_left]
  have h1 := mul_le_mul_of_nonneg_left (hx z hz) ha
  have h2 := mul_le_mul_of_nonneg_left (hy z hz) hb
  nlinarith

theorem voronoi_closed (L : Submodule ℤ E) : IsClosed (voronoi L) := by
  have he : voronoi L = ⋂ z : L, {x : E | ‖x‖ ≤ ‖x-(z:E)‖} := by
    ext x
    simp [voronoi]
  rw [he]
  exact isClosed_iInter fun z => isClosed_le continuous_norm (continuous_id.sub continuous_const).norm

theorem neg_mem_voronoi_iff (L : Submodule ℤ E) (x : E) :
    -x ∈ voronoi L ↔ x ∈ voronoi L := by
  rw [mem_voronoi_iff, mem_voronoi_iff]
  constructor <;> intro h z hz
  · have hh := h (-z) (L.neg_mem hz)
    simpa only [inner_neg_left, inner_neg_right, neg_neg, norm_neg] using hh
  · have hh := h (-z) (L.neg_mem hz)
    simpa only [inner_neg_left, inner_neg_right, norm_neg] using hh

def face (L : Submodule ℤ E) (z : E) : Set E :=
  {x | x ∈ voronoi L ∧ 2*⟪x,z⟫_ℝ = ‖z‖^2}

theorem face_eq_inter_translate {L : Submodule ℤ E} {z : E} (hz : z ∈ L) :
    face L z = {x | x ∈ voronoi L ∧ x-z ∈ voronoi L} := by
  ext x
  constructor
  · rintro ⟨hx, he⟩
    refine ⟨hx, ?_⟩
    have hn : ‖x-z‖ = ‖x‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [norm_sub_sq_real, he]
      ring
    intro w hw
    rw [hn]
    convert hx (z+w) (L.add_mem hz hw) using 1 <;> congr 1 <;> abel
  · rintro ⟨hx, hy⟩
    refine ⟨hx, ?_⟩
    have h1 := hx z hz
    have h2 := hy (-z) (L.neg_mem hz)
    have hn : ‖x‖ = ‖x-z‖ := le_antisymm h1 (by simpa using h2)
    have hs := norm_sub_sq_real x z
    rw [← hn] at hs
    linarith

theorem face_reflection {L : Submodule ℤ E} {z x : E} (hz : z ∈ L)
    (hx : x ∈ face L z) : z-x ∈ face L z := by
  rw [face_eq_inter_translate hz] at hx ⊢
  refine ⟨?_, ?_⟩
  · have h := (neg_mem_voronoi_iff L (x-z)).mpr hx.2
    simpa only [neg_sub] using h
  · have h := (neg_mem_voronoi_iff L x).mpr hx.1
    convert h using 1 <;> congr 1 <;> abel

theorem face_convex (L : Submodule ℤ E) (z : E) : Convex ℝ (face L z) := by
  intro x hx y hy a b ha hb hab
  refine ⟨voronoi_convex L hx.1 hy.1 ha hb hab, ?_⟩
  simp only [inner_add_left, real_inner_smul_left]
  nlinarith [hx.2, hy.2]

def tangent (z : E) : Submodule ℝ E := LinearMap.ker (innerSL ℝ z).toLinearMap

@[simp] theorem mem_tangent (z y : E) : y ∈ tangent z ↔ ⟪z,y⟫_ℝ = 0 := Iff.rfl

def base (L : Submodule ℤ E) (z : E) : Set (tangent z) :=
  {y | (1/2 : ℝ) • z + (y:E) ∈ voronoi L}

theorem base_point_mem_face {L : Submodule ℤ E} {z : E} {y : tangent z}
    (hy : y ∈ base L z) : (1/2 : ℝ) • z + (y:E) ∈ face L z := by
  refine ⟨hy, ?_⟩
  have ht : ⟪(y:E),z⟫_ℝ = 0 := by rw [real_inner_comm]; exact y.property
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, ht]
  ring

theorem base_convex (L : Submodule ℤ E) (z : E) : Convex ℝ (base L z) := by
  intro x hx y hy a b ha hb hab
  have h := voronoi_convex L hx hy ha hb hab
  have he : a • ((1/2 : ℝ) • z + (x:E)) + b • ((1/2 : ℝ) • z + (y:E)) =
      (1/2 : ℝ) • z + ((a • x + b • y : tangent z) : E) := by
    simp only [smul_add, smul_smul, Submodule.coe_add, Submodule.coe_smul]
    rw [add_add_add_comm, ← add_smul]
    congr 1
    rw [← add_mul, hab, one_mul]
  rwa [he] at h

theorem neg_mem_base_iff {L : Submodule ℤ E} {z : E} (hz : z ∈ L) (y : tangent z) :
    -y ∈ base L z ↔ y ∈ base L z := by
  have h (v : tangent z) (hv : v ∈ base L z) : -v ∈ base L z := by
    have hr := (face_reflection hz (base_point_mem_face hv)).1
    change (1/2 : ℝ) • z + ((-v : tangent z) : E) ∈ voronoi L
    convert hr using 1
    simp only [Submodule.coe_neg]
    module
  exact ⟨fun hy => by simpa using h (-y) hy, h y⟩

/-- Nonempty interior in the true bisector hyperplane is the facet condition. -/
def IsFacetVector (L : Submodule ℤ E) (z : E) : Prop :=
  z ∈ L ∧ z ≠ 0 ∧ (interior (base L z)).Nonempty

theorem facet_center_interior {L : Submodule ℤ E} {z : E} (hz : IsFacetVector L z) :
    (0 : tangent z) ∈ interior (base L z) := by
  obtain ⟨y, hy⟩ := hz.2.2
  have he : (Homeomorph.neg (tangent z)) ⁻¹' base L z = base L z := by
    ext v
    exact neg_mem_base_iff hz.1 v
  have hn : -y ∈ interior (base L z) := by
    have hh : -y ∈ (Homeomorph.neg (tangent z)) ⁻¹' interior (base L z) := by
      simpa using hy
    rw [(Homeomorph.neg (tangent z)).preimage_interior, he] at hh
    exact hh
  have h := (base_convex L z).interior hy hn (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  simpa using h

theorem facet_center_mem {L : Submodule ℤ E} {z : E} (hz : IsFacetVector L z) :
    (1/2 : ℝ) • z ∈ voronoi L := by
  have h := interior_subset (facet_center_interior hz)
  simpa only [base, mem_setOf_eq, Submodule.coe_zero, add_zero] using h

end D4.FacetGeometry
