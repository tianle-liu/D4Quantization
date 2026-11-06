import D4.PrincipalIntegral
import D4.PrincipalVoronoi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Upper lifted faces and almost disjoint projected tiles

Different supporting normals give projected tiles whose intersections lie
in proper affine hyperplanes. The proof works directly with the coefficient
box, and does not assume a polyhedral tiling theorem.
-/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

def reducedCost (h : Fin 10 → ℝ) (u : Vec) (e : Fin 10) : ℝ :=
  h e - dotProduct u (cone1Vectors e)

def liftedSupport (h w : Fin 10 → ℝ) (u : Vec) : ℝ :=
  ∑ e, w e * |reducedCost h u e|

def upperFace (h w : Fin 10 → ℝ) (u : Vec) : Set (Fin 10 → ℝ) :=
  {t | t ∈ Icc (-w) w ∧ ∀ e, reducedCost h u e * t e = w e * |reducedCost h u e|}

def upperTile (h w : Fin 10 → ℝ) (u : Vec) : Set Vec :=
  generatorMap '' upperFace h w u

theorem upperTile_subset_zonotope (h w : Fin 10 → ℝ) (u : Vec) :
    upperTile h w u ⊆ zonotope w := by
  rintro r ⟨t, ht, rfl⟩
  exact ⟨t, ht.1, rfl⟩

theorem upperFace_compact (h w : Fin 10 → ℝ) (u : Vec) : IsCompact (upperFace h w u) := by
  have hc : IsClosed {t : Fin 10 → ℝ | ∀ e, reducedCost h u e * t e = w e * |reducedCost h u e|} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro e
    exact isClosed_eq (continuous_const.mul (continuous_apply e)) continuous_const
  exact isCompact_Icc.inter_right hc

theorem upperTile_compact (h w : Fin 10 → ℝ) (u : Vec) : IsCompact (upperTile h w u) :=
  (upperFace_compact h w u).image generatorMap.continuous_of_finiteDimensional

theorem height_decomposition (h : Fin 10 → ℝ) (u : Vec) (t : Fin 10 → ℝ) :
    dotProduct h t = dotProduct u (generatorMap t) + ∑ e, reducedCost h u e * t e := by
  rw [generatorMap_dot, ← Finset.sum_add_distrib]
  unfold dotProduct at ⊢
  apply Finset.sum_congr rfl
  intro e _
  unfold reducedCost dotProduct
  ring

theorem upper_height_bound (h w : Fin 10 → ℝ) (u : Vec) {t : Fin 10 → ℝ}
    (ht : t ∈ Icc (-w) w) :
    dotProduct h t ≤ dotProduct u (generatorMap t) + liftedSupport h w u := by
  rw [height_decomposition]
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro e _
  calc
    reducedCost h u e * t e ≤ |reducedCost h u e * t e| := le_abs_self _
    _ = |reducedCost h u e| * |t e| := abs_mul _ _
    _ ≤ |reducedCost h u e| * w e :=
      mul_le_mul_of_nonneg_left (abs_le.mpr ⟨ht.1 e, ht.2 e⟩) (abs_nonneg _)
    _ = w e * |reducedCost h u e| := mul_comm _ _

theorem upper_height_eq (h w : Fin 10 → ℝ) (u : Vec) {t : Fin 10 → ℝ}
    (ht : t ∈ upperFace h w u) :
    dotProduct h t = dotProduct u (generatorMap t) + liftedSupport h w u := by
  rw [height_decomposition]
  congr 1
  exact Finset.sum_congr rfl (fun e _ => ht.2 e)

theorem upperTile_common_height (h w : Fin 10 → ℝ) (u v : Vec) {r : Vec}
    (hu : r ∈ upperTile h w u) (hv : r ∈ upperTile h w v) :
    dotProduct u r + liftedSupport h w u = dotProduct v r + liftedSupport h w v := by
  obtain ⟨s, hs, hsr⟩ := hu
  obtain ⟨t, ht, htr⟩ := hv
  have hst := upper_height_bound h w v hs.1
  have hts := upper_height_bound h w u ht.1
  rw [upper_height_eq h w u hs, hsr] at hst
  rw [upper_height_eq h w v ht, htr] at hts
  exact le_antisymm hst hts

def affineHyperplane (a : Vec) (b : ℝ) : AffineSubspace ℝ Vec where
  carrier := {r | dotProduct a r = b}
  smul_vsub_vadd_mem c x y z hx hy hz := by
    change dotProduct a (c • (x - y) + z) = b
    rw [dotProduct_add, dotProduct_smul, dotProduct_sub, hx, hy, hz]
    simp

theorem affineHyperplane_ne_top {a : Vec} (ha : a ≠ 0) (b : ℝ) :
    affineHyperplane a b ≠ ⊤ := by
  intro heq
  have h0 : dotProduct a (0 : Vec) = b := by
    have hm : (0 : Vec) ∈ affineHyperplane a b := by rw [heq]; trivial
    exact hm
  have haa : dotProduct a a = b := by
    have hm : a ∈ affineHyperplane a b := by rw [heq]; trivial
    exact hm
  have hz : dotProduct a a = 0 := by simpa only [dotProduct_zero] using haa.trans h0.symm
  exact ha ((dotProduct_self_eq_zero).mp hz)

theorem affineHyperplane_volume {a : Vec} (ha : a ≠ 0) (b : ℝ) :
    volume (affineHyperplane a b : Set Vec) = 0 :=
  Measure.addHaar_affineSubspace volume _ (affineHyperplane_ne_top ha b)

/-- Generic distinct upper normals give intersections of Lebesgue measure zero. -/
theorem upperTile_inter_volume (h w : Fin 10 → ℝ) {u v : Vec} (huv : u ≠ v) :
    volume (upperTile h w u ∩ upperTile h w v) = 0 := by
  apply measure_mono_null (t := (affineHyperplane (u-v)
    (liftedSupport h w v - liftedSupport h w u) : Set Vec))
  · intro r hr
    change dotProduct (u-v) r = liftedSupport h w v - liftedSupport h w u
    rw [sub_dotProduct]
    linarith [upperTile_common_height h w u v hr.1 hr.2]
  · exact affineHyperplane_volume (sub_ne_zero.mpr huv) _

theorem upperTiles_ae_cover {ι : Type*} [Fintype ι] (h w : Fin 10 → ℝ)
    (u : ι → Vec) (hu : Function.Injective u)
    (hvol : ∑ i, volume (upperTile h w (u i)) = volume (zonotope w)) :
    (⋃ i, upperTile h w (u i)) =ᵐ[volume] zonotope w := by
  have hd : Pairwise (fun i j => AEDisjoint volume (upperTile h w (u i)) (upperTile h w (u j))) :=
    fun i j hij => upperTile_inter_volume h w (hu.ne hij)
  have hm : ∀ i, MeasurableSet (upperTile h w (u i)) :=
    fun i => (upperTile_compact h w (u i)).measurableSet
  have hv : volume (⋃ i, upperTile h w (u i)) = volume (zonotope w) := by
    rw [measure_iUnion₀ hd (fun i => (hm i).nullMeasurableSet), tsum_fintype, hvol]
  exact ae_eq_of_subset_of_measure_ge
    (iUnion_subset (fun i => upperTile_subset_zonotope h w (u i))) hv.ge
    (MeasurableSet.iUnion hm).nullMeasurableSet (zonotope_isCompact w).measure_lt_top.ne

/-- Once the finite determinant/volume identity is checked, the actual integral
is the sum of the actual projected upper-face integrals. -/
theorem integral_zonotope_eq_sum_upperTiles {ι : Type*} [Fintype ι]
    (h w : Fin 10 → ℝ) (u : ι → Vec) (hu : Function.Injective u)
    (hvol : ∑ i, volume (upperTile h w (u i)) = volume (zonotope w))
    (f : Vec → ℝ) (hf : Continuous f) :
    (∫ r in zonotope w, f r) = ∑ i, ∫ r in upperTile h w (u i), f r := by
  have hd : Pairwise (fun i j => AEDisjoint volume (upperTile h w (u i)) (upperTile h w (u j))) :=
    fun i j hij => upperTile_inter_volume h w (hu.ne hij)
  rw [← setIntegral_congr_set (upperTiles_ae_cover h w u hu hvol)]
  rw [integral_iUnion_ae (fun i => (upperTile_compact h w (u i)).measurableSet.nullMeasurableSet) hd,
    tsum_fintype]
  apply hf.continuousOn.integrableOn_compact
  exact isCompact_iUnion (fun i => upperTile_compact h w (u i))

end D4.Principal
