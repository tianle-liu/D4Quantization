import D4.NearestPoint
import D4.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The genuine Voronoi region in Gram coordinates

The inequalities range over every integer vector. We prove coverage,
null overlap of translates, unit volume, and the actual integral identity.
No secondary-cone classification or moment-polynomial identity is used.
-/
noncomputable section
open Matrix MeasureTheory Set
open scoped Pointwise

namespace D4.Analytic

attribute [local instance] integerTranslation

local instance : MeasurableConstVAdd IntVec Vec where
  measurable_const_vadd _ := (continuous_const.add continuous_id).measurable

local instance : MeasurableVAdd IntVec Vec where
  measurable_const_vadd _ := (continuous_const.add continuous_id).measurable
  measurable_vadd_const _ := measurable_of_countable _

local instance : VAddInvariantMeasure IntVec Vec volume where
  measure_preimage_vadd z s hs := by
    change volume ((fun x : Vec => castVec z + x) ⁻¹' s) = volume s
    exact measure_preimage_add volume (castVec z) s

/-- The Voronoi cell at zero, in coordinates for the quadratic form. -/
def voronoi (Q : Gram) : Set Vec :=
  {x | ∀ z : IntVec, quadratic Q x ≤ quadratic Q (x - castVec z)}

theorem voronoi_closed (Q : Gram) : IsClosed (voronoi Q) := by
  change IsClosed {x | ∀ z : IntVec, quadratic Q x ≤ quadratic Q (x - castVec z)}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro z
  exact isClosed_le (quadratic_continuous Q)
    ((quadratic_continuous Q).comp (continuous_id.sub continuous_const))

theorem nearest_eq_quadratic_on_voronoi {Q : Gram} (hQ : Q.PosSemidef)
    {x : Vec} (hx : x ∈ voronoi Q) : nearest Q x = quadratic Q x :=
  le_antisymm (nearest_le_quadratic hQ x) (le_ciInf hx)

theorem castVec_injective : Function.Injective castVec := by
  intro z w h
  ext i
  exact Int.cast_injective (congrFun h i)

theorem quadratic_pair_symmetric {Q : Gram} (hQ : Q.IsHermitian) (x y : Vec) :
    dotProduct x (Q *ᵥ y) = dotProduct y (Q *ᵥ x) := by
  have ht : Qᵀ = Q := by simpa only [conjTranspose_eq_transpose_of_trivial] using hQ.eq
  rw [dotProduct_mulVec, ← mulVec_transpose, ht, dotProduct_comm]

theorem quadratic_sub_vec {Q : Gram} (hQ : Q.IsHermitian) (x y : Vec) :
    quadratic Q (x-y) = quadratic Q x - 2 * dotProduct x (Q *ᵥ y) + quadratic Q y := by
  simp only [quadratic, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
  rw [quadratic_pair_symmetric hQ y x]
  ring

/-- A bisector is a proper affine hyperplane for a positive-definite form. -/
theorem quadratic_bisector_null {Q : Gram} (hQ : Q.PosDef) {y : Vec} (hy : y ≠ 0) :
    volume {x : Vec | quadratic Q x = quadratic Q (x-y)} = 0 := by
  let s : AffineSubspace ℝ Vec := {
    carrier := {x | dotProduct x (Q *ᵥ y) = quadratic Q y / 2}
    smul_vsub_vadd_mem := by
      intro c p₁ p₂ p₃ h₁ h₂ h₃
      change dotProduct (c • (p₁-p₂) + p₃) (Q *ᵥ y) = quadratic Q y / 2
      simp only [add_dotProduct, smul_dotProduct, sub_dotProduct, smul_eq_mul]
      rw [h₁, h₂, h₃]
      ring }
  have hs : s ≠ ⊤ := by
    intro he
    have hz : (0 : Vec) ∈ s := by rw [he]; trivial
    change dotProduct (0 : Vec) (Q *ᵥ y) = quadratic Q y / 2 at hz
    simp only [zero_dotProduct] at hz
    have hp : 0 < quadratic Q y := by simpa only [quadratic, star_trivial] using hQ.2 y hy
    linarith
  have heq : {x : Vec | quadratic Q x = quadratic Q (x-y)} = (s : Set Vec) := by
    ext x
    change quadratic Q x = quadratic Q (x-y) ↔ dotProduct x (Q *ᵥ y) = quadratic Q y / 2
    rw [quadratic_sub_vec hQ.1]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact Measure.addHaar_affineSubspace volume s hs

theorem voronoi_covers {Q : Gram} (hQ : Q.PosDef) (x : Vec) :
    ∃ z : IntVec, z +ᵥ x ∈ voronoi Q := by
  obtain ⟨z, hz⟩ := nearest_point_exists hQ x
  refine ⟨-z, ?_⟩
  change ∀ w : IntVec, quadratic Q (castVec (-z) + x) ≤
    quadratic Q (castVec (-z) + x - castVec w)
  intro w
  convert hz (z+w) using 1 <;> congr 1 <;> ext i <;> simp [castVec] <;> ring

theorem voronoi_translate_null_overlap {Q : Gram} (hQ : Q.PosDef)
    {z : IntVec} (hz : z ≠ 0) : AEDisjoint volume (z +ᵥ voronoi Q) (voronoi Q) := by
  apply measure_mono_null (t := {x : Vec | quadratic Q x = quadratic Q (x-castVec z)})
  · rintro x ⟨⟨y, hy, rfl⟩, hx⟩
    have hxy := hx z
    have hyx := hy (-z)
    change quadratic Q (castVec z + y) ≤ quadratic Q (castVec z + y - castVec z) at hxy
    change quadratic Q y ≤ quadratic Q (y - castVec (-z)) at hyx
    change quadratic Q (castVec z + y) = quadratic Q (castVec z + y - castVec z)
    have h₁ : castVec z + y - castVec z = y := by abel
    have h₂ : y - castVec (-z) = castVec z + y := by ext i; simp [castVec]; ring
    rw [h₁] at hxy ⊢
    rw [h₂] at hyx
    exact le_antisymm hxy hyx
  · apply quadratic_bisector_null hQ
    intro he
    apply hz
    apply castVec_injective
    exact he.trans (by ext i; simp [castVec])

theorem voronoi_fundamental {Q : Gram} (hQ : Q.PosDef) :
    IsAddFundamentalDomain IntVec (voronoi Q) volume := by
  apply IsAddFundamentalDomain.mk'' (voronoi_closed Q).measurableSet.nullMeasurableSet
    (Filter.Eventually.of_forall (voronoi_covers hQ))
  · intro z hz
    exact voronoi_translate_null_overlap hQ hz
  · intro z
    exact (measurePreserving_vadd z volume).quasiMeasurePreserving

/-- The true Voronoi region has covolume one in integer coordinates. -/
theorem voronoi_volume {Q : Gram} (hQ : Q.PosDef) : volume (voronoi Q) = 1 := by
  rw [(voronoi_fundamental hQ).measure_eq halfOpenCube_fundamental,
    measure_congr halfOpenCube_ae_unitCube, unitCube_volume]

/-- The actual second-moment integral on the closed Voronoi cell. -/
theorem moment_eq_voronoi {Q : Gram} (hQ : Q.PosDef) :
    moment Q = ∫ x in voronoi Q, quadratic Q x := by
  rw [moment_eq_fundamentalDomain Q (voronoi_fundamental hQ)]
  apply setIntegral_congr_fun (voronoi_closed Q).measurableSet
  exact fun _ hx => nearest_eq_quadratic_on_voronoi hQ.posSemidef hx

end D4.Analytic
