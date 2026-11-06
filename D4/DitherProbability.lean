import D4.DitherIntegral
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace D4.FacetGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

def uniformVoronoi : Measure E := (volume (voronoi L))⁻¹ • volume.restrict (voronoi L)

theorem voronoi_volume_pos : 0 < volume (voronoi L) :=
  Measure.measure_pos_of_nonempty_interior volume ⟨0,zero_mem_interior_voronoi (L := L)⟩

instance uniformVoronoi_probability : IsProbabilityMeasure (uniformVoronoi L) where
  measure_univ := by
    simp only [uniformVoronoi, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (voronoi_volume_pos L).ne' (voronoi_compact_full (L := L)).measure_ne_top

theorem dither_measurePreserving (Q : E → L) (hQm : Measurable Q)
    (hQ : ∀ x, x-(Q x:E) ∈ voronoi L) (a : E) :
    MeasurePreserving (fun u => a+u-(Q (a+u):E))
      (volume.restrict (voronoi L)) (volume.restrict (voronoi L)) := by
  have hm : Measurable (fun u => a+u-(Q (a+u):E)) :=
    (measurable_const.add measurable_id).sub
      (measurable_subtype_coe.comp (hQm.comp (measurable_const.add measurable_id)))
  refine ⟨hm, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm]
  exact dither_lintegral L f Q hQ a

theorem dither_uniform (Q : E → L) (hQm : Measurable Q)
    (hQ : ∀ x, x-(Q x:E) ∈ voronoi L) (a : E) :
    MeasurePreserving (fun u => a+u-(Q (a+u):E)) (uniformVoronoi L) (uniformVoronoi L) :=
  (dither_measurePreserving L Q hQm hQ a).smul_measure _

theorem neg_uniformVoronoi :
    MeasurePreserving (fun x : E => -x) (uniformVoronoi L) (uniformVoronoi L) := by
  have he : (fun x : E => -x) ⁻¹' voronoi L = voronoi L := by
    ext x; exact neg_mem_voronoi_iff L x
  have hh := (Measure.measurePreserving_neg (volume : Measure E)).restrict_preimage
    (voronoi_closed L).measurableSet
  rw [he] at hh
  exact hh.smul_measure _

/-- The actual subtractive-dither error, with the paper's sign convention. -/
def ditherError (Q : E → L) (a u : E) : E := (Q (a+u):E)-u-a

theorem subtractive_dither_uniform (Q : E → L) (hQm : Measurable Q)
    (hQ : ∀ x, x-(Q x:E) ∈ voronoi L) (a : E) :
    MeasurePreserving (ditherError L Q a) (uniformVoronoi L) (uniformVoronoi L) := by
  have hh := (neg_uniformVoronoi L).comp (dither_uniform L Q hQm hQ a)
  convert hh using 1
  funext u
  simp only [Function.comp_apply, ditherError, neg_sub]
  abel

/-- For any input law, the joint input/error law is the product of that input
law and uniform measure on the actual Voronoi cell. -/
theorem subtractive_dither_joint (Q : E → L) (hQm : Measurable Q)
    (hQ : ∀ x, x-(Q x:E) ∈ voronoi L) (μ : Measure E) [SFinite μ]
    :
    MeasurePreserving (fun p : E × E => (p.1, ditherError L Q p.1 p.2))
      (μ.prod (uniformVoronoi L)) (μ.prod (uniformVoronoi L)) := by
  apply (MeasurePreserving.id μ).skew_product
  · exact ((measurable_subtype_coe.comp (hQm.comp
      (measurable_fst.add measurable_snd))).sub measurable_snd).sub measurable_fst
  · exact Filter.Eventually.of_forall fun a => (subtractive_dither_uniform L Q hQm hQ a).map_eq

/-- Arbitrary random input independent of uniform dither has uniform error,
and the error is independent of that input. -/
theorem subtractive_dither_independent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X U : Ω → E)
    (hX : Measurable X) (hU : Measurable U) (hind : IndepFun X U P)
    (huniform : P.map U = uniformVoronoi L)
    (Q : E → L) (hQm : Measurable Q) (hQ : ∀ x, x-(Q x:E) ∈ voronoi L) :
    P.map (fun ω => ditherError L Q (X ω) (U ω)) = uniformVoronoi L ∧
    IndepFun X (fun ω => ditherError L Q (X ω) (U ω)) P := by
  letI : IsProbabilityMeasure (P.map X) := isProbabilityMeasure_map hX.aemeasurable
  have he : Measurable (fun ω => ditherError L Q (X ω) (U ω)) :=
    ((measurable_subtype_coe.comp (hQm.comp (hX.add hU))).sub hU).sub hX
  have hp : MeasurePreserving (fun ω => (X ω,U ω)) P
      ((P.map X).prod (uniformVoronoi L)) := by
    refine ⟨hX.prodMk hU, ?_⟩
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hU.aemeasurable).mp hind,
      huniform]
  have hj := ((subtractive_dither_joint L Q hQm hQ (P.map X)).comp hp).map_eq
  change P.map (fun ω => (X ω,ditherError L Q (X ω) (U ω))) =
      (P.map X).prod (uniformVoronoi L) at hj
  have hm : P.map (fun ω => ditherError L Q (X ω) (U ω)) = uniformVoronoi L := by
    have hh := congrArg Measure.snd hj
    simpa only [Measure.snd_map_prodMk hX, Measure.snd_prod] using hh
  refine ⟨hm, ?_⟩
  apply (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable he.aemeasurable).mpr
  rw [hm]
  exact hj

end D4.FacetGeometry
