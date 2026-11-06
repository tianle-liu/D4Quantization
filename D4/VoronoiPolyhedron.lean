import D4.VoronoiLatticeCompact
import Mathlib.Analysis.InnerProductSpace.Dual

/-! The infinite nearest-point cell has an exact finite halfspace description. -/
noncomputable section
open Set Module
open scoped InnerProductSpace
namespace D4.FacetGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

theorem basis_halfspaces_bounded : ∃ C : ℝ, ∀ x : E,
    (∀ i, 2*⟪x,((b i : L):E)⟫_ℝ ≤ ‖((b i : L):E)‖^2) →
    (∀ i, 2*⟪x,-((b i : L):E)⟫_ℝ ≤ ‖((b i : L):E)‖^2) → ‖x‖ ≤ C := by
  let br := b.ofZLatticeBasis ℝ L
  let f : E →ₗ[ℝ] (ι → ℝ) := LinearMap.pi fun i => (innerSL ℝ (br i)).toLinearMap
  have hf : Function.Injective f := by
    intro x y h
    exact InnerProductSpace.ext_inner_left_basis br (fun i => congrFun h i)
  obtain ⟨K, hK, hk⟩ := f.injective_iff_antilipschitz.mp hf
  let C : ℝ := ∑ i, ‖((b i:L):E)‖^2
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨K*C, ?_⟩
  intro x hp hn
  have hfn : ‖f x‖ ≤ C := by
    apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro i
    change ‖⟪br i,x⟫_ℝ‖ ≤ C
    rw [Real.norm_eq_abs]
    simp only [br, Basis.ofZLatticeBasis_apply]
    have hp' := hp i
    have hn' := hn i
    rw [inner_neg_right] at hn'
    have hc : ‖((b i:L):E)‖^2 ≤ C :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖((b j:L):E)‖) (Finset.mem_univ i)
    rw [real_inner_comm]
    apply abs_le.mpr
    constructor <;> linarith
  have h := hk.le_mul_dist x 0
  rw [map_zero, dist_zero_right, dist_zero_right] at h
  exact h.trans (mul_le_mul_of_nonneg_left hfn K.coe_nonneg)

include b

/-- The listed competitors are actual nonzero lattice points, and suffice everywhere. -/
theorem exists_finite_voronoi_halfspaces : ∃ T : Finset E,
    (∀ z ∈ T, z ∈ L ∧ z ≠ 0) ∧
    ∀ x : E, x ∈ voronoi L ↔ ∀ z ∈ T, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2 := by
  classical
  obtain ⟨C, hC⟩ := basis_halfspaces_bounded b
  let S : ℝ := ∑ i, ‖((b i:L):E)‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let R : ℝ := max C S + 1
  have hCR : C ≤ R := by dsimp [R]; linarith [le_max_left C S]
  have hSR : S ≤ R := by dsimp [R]; linarith [le_max_right C S]
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right C S]
  have hclosed : IsClosed (L : Set E) := by
    letI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
    change IsClosed (L.toAddSubgroup : Set E)
    exact AddSubgroup.isClosed_of_discrete
  have hfin : Set.Finite (Metric.closedBall (0:E) (2*R) ∩ (L:Set E)) :=
    Metric.finite_isBounded_inter_isClosed (Metric.isBounded_closedBall) hclosed
  let T : Finset E := hfin.toFinset.erase 0
  have hmem (z : E) : z ∈ T ↔ z ∈ L ∧ z ≠ 0 ∧ ‖z‖ ≤ 2*R := by
    simp only [T, Finset.mem_erase, Set.Finite.mem_toFinset, mem_inter_iff,
      Metric.mem_closedBall, dist_zero_right]
    tauto
  refine ⟨T, fun z hz => ⟨(hmem z).mp hz |>.1, (hmem z).mp hz |>.2.1⟩, ?_⟩
  intro x
  constructor
  · intro hx z hz
    exact (mem_voronoi_iff L x).mp hx z ((hmem z).mp hz).1
  · intro hx
    have hsmall (z : E) (hz : z ∈ L) (hn : ‖z‖ ≤ 2*R) : 2*⟪x,z⟫_ℝ ≤ ‖z‖^2 := by
      by_cases hz0 : z = 0
      · simp [hz0]
      · exact hx z ((hmem z).mpr ⟨hz, hz0, hn⟩)
    have hb (i : ι) : ‖((b i:L):E)‖ ≤ 2*R := by
      have hi : ‖((b i:L):E)‖ ≤ S :=
        Finset.single_le_sum (fun j _ => norm_nonneg ((b j:L):E)) (Finset.mem_univ i)
      linarith
    have hbn (i : ι) : 2*⟪x,-((b i:L):E)⟫_ℝ ≤ ‖((b i:L):E)‖^2 := by
      have ht := hsmall (-((b i:L):E)) (L.neg_mem (b i).property)
        (by simpa only [norm_neg] using hb i)
      simpa only [norm_neg] using ht
    have hxn : ‖x‖ ≤ R := (hC x (fun i => hsmall _ (b i).property (hb i)) hbn).trans hCR
    rw [mem_voronoi_iff]
    intro z hz
    by_cases hn : ‖z‖ ≤ 2*R
    · exact hsmall z hz hn
    · have hi := real_inner_le_norm x z
      have hp : 0 ≤ ‖z‖ * (‖z‖ - 2*‖x‖) :=
        mul_nonneg (norm_nonneg _) (by linarith)
      nlinarith

omit b in
theorem exists_finite_voronoi_halfspaces_full : ∃ T : Finset E,
    (∀ z ∈ T, z ∈ L ∧ z ≠ 0) ∧
    ∀ x : E, x ∈ voronoi L ↔ ∀ z ∈ T, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2 := by
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  exact exists_finite_voronoi_halfspaces (Module.Free.chooseBasis ℤ L)

omit b in
theorem frontier_has_active_vector {T : Finset E}
    (hT : ∀ x : E, x ∈ voronoi L ↔ ∀ z ∈ T, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2)
    {x : E} (hx : x ∈ frontier (voronoi L)) : ∃ z ∈ T, x ∈ face L z := by
  classical
  have hxV : x ∈ voronoi L := (voronoi_closed L).frontier_subset hx
  by_contra! hn
  let U : Set E := {y | ∀ z : T, 2*⟪y,(z:E)⟫_ℝ < ‖(z:E)‖^2}
  have hU : IsOpen U := by
    simp only [U, setOf_forall]
    exact isOpen_iInter_of_finite fun z =>
      isOpen_lt (continuous_const.mul (continuous_id.inner continuous_const)) continuous_const
  have hxU : x ∈ U := by
    intro z
    refine lt_of_le_of_ne ((hT x).mp hxV z z.property) ?_
    intro he
    exact hn z z.property ⟨hxV, he⟩
  have hUV : U ⊆ voronoi L := by
    intro y hy
    apply (hT y).mpr
    intro z hz
    exact (hy ⟨z,hz⟩).le
  have hxi : x ∈ interior (voronoi L) := interior_maximal hUV hU hxU
  exact hx.2 hxi

end D4.FacetGeometry
