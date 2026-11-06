import D4.VoronoiPyramidNull
import D4.ConeAnalysisFacetNull
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace Topology
namespace D4.FacetGeometry
attribute [local instance] Classical.propDecidable

/-- Finite integration with intersections allowed on null sets. -/
theorem integral_finset_biUnion_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ι : Type*} (t : Finset ι) {S : ι → Set X} {f : X → ℝ}
    (hS : ∀ i ∈ t, MeasurableSet (S i))
    (hpair : Set.Pairwise (↑t) (fun i j => AEDisjoint μ (S i) (S j)))
    (hf : ∀ i ∈ t, IntegrableOn f (S i) μ) :
    ∫ x in ⋃ i ∈ t, S i, f x ∂μ = ∑ i ∈ t, ∫ x in S i, f x ∂μ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    simp only [Finset.forall_mem_insert] at hS hf
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
    have hp : Set.Pairwise (↑t) (fun i j => AEDisjoint μ (S i) (S j)) :=
      hpair.mono (by simp)
    rw [integral_union_ae, ih hS.2 hp hf.2]
    · change μ (S i ∩ ⋃ j ∈ t, S j) = 0
      simp only [inter_iUnion]
      apply (measure_biUnion_null_iff t.countable_toSet).mpr
      intro j hj
      exact hpair (by simp) (by simp [hj]) (ne_of_mem_of_not_mem hj hi).symm
    · exact (Finset.measurableSet_biUnion t hS.2).nullMeasurableSet
    · exact hf.1
    · exact integrableOn_finset_iUnion.mpr hf.2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

 theorem voronoi_ae_pyramid_union [Nontrivial E] {T : Finset E}
    (hT : ∀ x : E, x ∈ voronoi L ↔ ∀ z ∈ T, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2) :
    voronoi L =ᵐ[volume] ⋃ z ∈ T, closedPyramid L z := by
  apply ae_eq_set.mpr
  constructor
  · apply measure_mono_null (t := {(0:E)}) _ (measure_singleton 0)
    intro x hx
    rcases voronoi_finite_pyramid_cover hT hx.1 with h | h
    · exact h
    · exact (hx.2 h).elim
  · have he : (⋃ z ∈ T, closedPyramid L z) ⊆ voronoi L := by
      intro x hx
      rcases mem_iUnion.mp hx with ⟨z, hz⟩
      rcases mem_iUnion.mp hz with ⟨_, hp⟩
      exact closedPyramid_subset_voronoi L z hp
    rw [diff_eq_empty.mpr he, measure_empty]

 theorem voronoi_integral_eq_sum_pyramids [Nontrivial E] {T : Finset E}
    (hmem : ∀ z ∈ T, z ∈ L ∧ z ≠ 0)
    (hT : ∀ x : E, x ∈ voronoi L ↔ ∀ z ∈ T, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2)
    {f : E → ℝ} (hf : Continuous f) :
    ∫ x in voronoi L, f x = ∑ z ∈ T, ∫ x in pyramid L z, f x := by
  rw [setIntegral_congr_set (voronoi_ae_pyramid_union hT)]
  rw [integral_finset_biUnion_ae T]
  · apply Finset.sum_congr rfl
    intro z hz
    exact setIntegral_congr_set (closedPyramid_ae_eq_pyramid (hmem z hz).2)
  · exact fun z _ => (closedPyramid_compact z).measurableSet
  · intro z hz w hw hne
    exact closedPyramid_inter_volume_zero (hmem z hz).1 (hmem w hw).1
      (hmem z hz).2 (hmem w hw).2 hne
  · exact fun z _ => hf.continuousOn.integrableOn_compact (closedPyramid_compact z)


theorem voronoi_integral_eq_sum_facets [Nontrivial E] {T : Finset E}
    (hmem : ∀ z ∈ T, z ∈ L ∧ z ≠ 0)
    (hT : ∀ x : E, x ∈ voronoi L ↔ ∀ z ∈ T, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2)
    {f : E → ℝ} (hf : Continuous f) :
    ∫ x in voronoi L, f x =
      ∑ z ∈ T.filter (IsFacetVector L), ∫ x in pyramid L z, f x := by
  classical
  rw [voronoi_integral_eq_sum_pyramids hmem hT hf, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs with h
  · rfl
  · exact setIntegral_zero_measure _
      (D4.ConeAnalysis.nonfacet_pyramid_volume_zero (hmem z hz).1 (hmem z hz).2 h)

theorem selected_facets_card_le {T : Finset E}
    (hmem : ∀ z ∈ T, z ∈ L ∧ z ≠ 0) :
    (T.filter (IsFacetVector L)).card ≤ Nat.card (FacetVectors L) := by
  classical
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  letI := finite_facetVectors (Module.Free.chooseBasis ℤ L)
  letI := Fintype.ofFinite (FacetVectors L)
  let f : (T.filter (IsFacetVector L)) → FacetVectors L := fun z =>
    ⟨⟨(z:E), (hmem z (Finset.mem_filter.mp z.property).1).1⟩,
      (Finset.mem_filter.mp z.property).2⟩
  have hf : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    exact congrArg (fun v : FacetVectors L => ((v.val:L):E)) he
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem selected_facets_card_bound {T : Finset E}
    (hmem : ∀ z ∈ T, z ∈ L ∧ z ≠ 0) :
    (T.filter (IsFacetVector L)).card ≤ 2*(2^Module.finrank ℝ E-1) :=
  (selected_facets_card_le hmem).trans card_facetVectors_le_finrank

theorem voronoi_volume_eq_sum_facets [Nontrivial E] {T : Finset E}
    (hmem : ∀ z ∈ T, z ∈ L ∧ z ≠ 0)
    (hT : ∀ x : E, x ∈ voronoi L ↔ ∀ z ∈ T, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2) :
    volume.real (voronoi L) =
      ∑ z ∈ T.filter (IsFacetVector L), volume.real (pyramid L z) := by
  simpa using voronoi_integral_eq_sum_facets hmem hT
    (continuous_const : Continuous (fun _ : E => (1:ℝ)))

theorem voronoi_secondMoment_eq_sum_facets [Nontrivial E] {T : Finset E}
    (hmem : ∀ z ∈ T, z ∈ L ∧ z ≠ 0)
    (hT : ∀ x : E, x ∈ voronoi L ↔ ∀ z ∈ T, 2*⟪x,z⟫_ℝ ≤ ‖z‖^2) :
    (∫ x in voronoi L, ‖x‖^2) =
      ∑ z ∈ T.filter (IsFacetVector L), ∫ x in pyramid L z, ‖x‖^2 :=
  voronoi_integral_eq_sum_facets hmem hT (continuous_norm.pow 2)

end D4.FacetGeometry
