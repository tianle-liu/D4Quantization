import D4.VoronoiQuantizer
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal
namespace D4.FacetGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- Periodization of an arbitrary nonnegative function on the actual Voronoi cell. -/
def orbitSum (f : E → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  ∑' z : L, (voronoi L).indicator f (x-(z:E))

theorem orbitSum_periodic (f : E → ℝ≥0∞) (z : L) (x : E) :
    orbitSum L f ((z:E)+x) = orbitSum L f x := by
  unfold orbitSum
  rw [← (Equiv.addLeft z).tsum_eq]
  apply tsum_congr
  intro w
  congr 1
  change (z:E)+x-((z:E)+(w:E)) = x-(w:E)
  abel

theorem ae_unique_voronoi_translate : ∀ᵐ x : E ∂volume,
    ∀ z w : L, x-(z:E) ∈ voronoi L → x-(w:E) ∈ voronoi L → z=w := by
  apply ae_all_iff.mpr
  intro z
  apply ae_all_iff.mpr
  intro w
  by_cases hzw : z=w
  · exact Filter.Eventually.of_forall fun _ _ _ => hzw
  have hh := (voronoi_fundamental_lattice L).aedisjoint hzw
  have hn : ∀ᵐ x : E ∂volume, x ∉ (z +ᵥ voronoi L) ∩ (w +ᵥ voronoi L) := by
    simpa only [ae_iff, not_not] using hh
  filter_upwards [hn] with x hx hz hw
  exfalso
  apply hx
  constructor
  · refine ⟨x-(z:E), hz, ?_⟩
    change (z:E)+(x-(z:E))=x
    abel
  · refine ⟨x-(w:E), hw, ?_⟩
    change (w:E)+(x-(w:E))=x
    abel

theorem orbitSum_eq_quantizer_ae (f : E → ℝ≥0∞) (Q : E → L)
    (hQ : ∀ x, x-(Q x:E) ∈ voronoi L) :
    orbitSum L f =ᵐ[volume] fun x => f (x-(Q x:E)) := by
  classical
  filter_upwards [ae_unique_voronoi_translate L] with x hx
  unfold orbitSum
  rw [tsum_eq_single (Q x)]
  · exact indicator_of_mem (hQ x) f
  · intro z hz
    apply indicator_of_not_mem
    intro hm
    exact hz (hx z (Q x) hm (hQ x))

theorem orbitSum_eq_on_voronoi_ae (f : E → ℝ≥0∞) :
    orbitSum L f =ᵐ[volume.restrict (voronoi L)] f := by
  classical
  filter_upwards [(ae_unique_voronoi_translate L).filter_mono ae_restrict_le,
    ae_restrict_mem (voronoi_closed L).measurableSet] with x hx hV
  unfold orbitSum
  rw [tsum_eq_single (0:L)]
  · simpa using indicator_of_mem hV f
  · intro z hz
    apply indicator_of_not_mem
    intro hm
    exact hz (hx z 0 hm (by simpa using hV))

theorem orbitSum_integral_fundamental (f : E → ℝ≥0∞) {s : Set E}
    (hs : IsAddFundamentalDomain L s volume) :
    ∫⁻ x in s, orbitSum L f x = ∫⁻ x in voronoi L, f x := by
  rw [hs.setLIntegral_eq (voronoi_fundamental_lattice L) (orbitSum L f)
    (fun z x => orbitSum_periodic L f z x)]
  exact lintegral_congr_ae (orbitSum_eq_on_voronoi_ae L f)

theorem translated_voronoi_fundamental (a : E) :
    IsAddFundamentalDomain L ((fun x : E => x-a) ⁻¹' voronoi L) volume := by
  apply (voronoi_fundamental_lattice L).preimage_of_equiv
    (measurePreserving_sub_right volume a).quasiMeasurePreserving (e := fun z : L => z)
    Function.bijective_id
  intro z x
  change (z:E)+x-a=(z:E)+(x-a)
  abel

/-- Translation followed by any measurable nearest-lattice quantizer preserves
uniform integration on the Voronoi cell. The input translation is arbitrary. -/
theorem dither_lintegral (f : E → ℝ≥0∞) (Q : E → L)
    (hQ : ∀ x, x-(Q x:E) ∈ voronoi L) (a : E) :
    ∫⁻ u in voronoi L, f (a+u-(Q (a+u):E)) =
      ∫⁻ u in voronoi L, f u := by
  have hae : (fun u => orbitSum L f (a+u)) =ᵐ[volume]
      (fun u => f (a+u-(Q (a+u):E))) :=
    (measurePreserving_add_left volume a).quasiMeasurePreserving.ae
      (orbitSum_eq_quantizer_ae L f Q hQ)
  calc
    ∫⁻ u in voronoi L, f (a+u-(Q (a+u):E)) =
        ∫⁻ u in voronoi L, orbitSum L f (a+u) := by
      apply lintegral_congr_ae
      exact hae.symm.filter_mono ae_restrict_le
    _ = ∫⁻ x in ((fun x : E => x-a) ⁻¹' voronoi L), orbitSum L f x := by
      have he : (fun x : E => x-a) ⁻¹' voronoi L =
          (fun x : E => a+x) '' voronoi L := by
        ext x
        constructor
        · intro hx; exact ⟨x-a, hx, by change a+(x-a)=x; abel⟩
        · rintro ⟨y,hy,rfl⟩
          change a+y-a ∈ voronoi L
          simpa only [add_sub_cancel_left] using hy
      rw [he]
      exact (measurePreserving_add_left volume a).setLIntegral_comp_emb
        (Homeomorph.addLeft a).measurableEmbedding _ _
    _ = _ := orbitSum_integral_fundamental L f (translated_voronoi_fundamental L a)

end D4.FacetGeometry
