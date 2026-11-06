import D4.VoronoiPyramidNull
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Group.FundamentalDomain

noncomputable section
open Set MeasureTheory
open scoped Pointwise
namespace D4.FacetGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

instance latticeMeasurableVAdd : MeasurableVAdd L E where
  measurable_const_vadd z := (continuous_const.add continuous_id).measurable
  measurable_vadd_const x := measurable_of_countable _

instance latticeVAddInvariant : VAddInvariantMeasure L E volume where
  measure_preimage_vadd z s hs := by
    change volume ((fun x : E => (z:E)+x) ⁻¹' s) = volume s
    exact measure_preimage_add volume (z:E) s

theorem lattice_closed : IsClosed (L : Set E) := by
  letI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  change IsClosed (L.toAddSubgroup : Set E)
  exact AddSubgroup.isClosed_of_discrete

theorem nearest_lattice_exists (x : E) :
    ∃ z : L, x-(z:E) ∈ voronoi L := by
  obtain ⟨z, hz, he⟩ := (lattice_closed L).exists_infDist_eq_dist ⟨0,L.zero_mem⟩ x
  refine ⟨⟨z,hz⟩, ?_⟩
  intro w hw
  have hh := Metric.infDist_le_dist_of_mem (x := x) (L.add_mem hz hw)
  rw [he, dist_eq_norm, dist_eq_norm] at hh
  convert hh using 1 <;> congr 1 <;> abel

theorem voronoi_covers_lattice (x : E) : ∃ z : L, z +ᵥ x ∈ voronoi L := by
  obtain ⟨z,hz⟩ := nearest_lattice_exists L x
  refine ⟨-z, ?_⟩
  change -(z:E)+x ∈ voronoi L
  simpa only [sub_eq_add_neg, add_comm] using hz

theorem voronoi_translate_null {z : L} (hz : z ≠ 0) :
    AEDisjoint volume (z +ᵥ voronoi L) (voronoi L) := by
  have hzE : (z:E) ≠ 0 := fun h => hz (Subtype.ext h)
  apply measure_mono_null (t := face L (z:E))
  · rintro x ⟨⟨y,hy,rfl⟩,hx⟩
    rw [face_eq_inter_translate z.property]
    refine ⟨hx, ?_⟩
    change (z:E) + y - (z:E) ∈ voronoi L
    simpa only [add_sub_cancel_left] using hy
  · exact face_volume_zero hzE

theorem voronoi_fundamental_lattice : IsAddFundamentalDomain L (voronoi L) volume := by
  apply IsAddFundamentalDomain.mk'' (voronoi_closed L).measurableSet.nullMeasurableSet
    (Filter.Eventually.of_forall (voronoi_covers_lattice L))
  · exact fun z hz => voronoi_translate_null L hz
  · intro z
    exact (measurePreserving_vadd z volume).quasiMeasurePreserving

/-- A measurable nearest-lattice quantizer exists, with a fixed measurable tie rule. -/
theorem exists_measurable_quantizer :
    ∃ Q : E → L, Measurable Q ∧ ∀ x, x-(Q x:E) ∈ voronoi L := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat L
  have hex : ∀ x : E, ∃ n : ℕ, x-(e n:E) ∈ voronoi L := by
    intro x
    obtain ⟨z,hz⟩ := nearest_lattice_exists L x
    obtain ⟨n,rfl⟩ := he z
    exact ⟨n,hz⟩
  refine ⟨fun x => e (Nat.find (hex x)), ?_, ?_⟩
  · apply (measurable_of_countable e).comp
    apply measurable_find hex
    intro n
    exact (voronoi_closed L).measurableSet.preimage
      (continuous_id.sub continuous_const).measurable
  · exact fun x => Nat.find_spec (hex x)

end D4.FacetGeometry
