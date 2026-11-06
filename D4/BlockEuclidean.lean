import D4.BlockProductIntegral
import D4.VoronoiLatticeCompact
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Cartesian products represented in a genuine Euclidean space. -/
noncomputable section
namespace D4.Blocks
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Concatenate orthogonal coordinate blocks. -/
def blockJoin : (ι → EuclideanSpace ℝ κ) ≃ₗ[ℝ] EuclideanSpace ℝ (ι × κ) where
  toFun x := (WithLp.equiv 2 (ι × κ → ℝ)).symm (fun p => x p.1 p.2)
  invFun x i := (WithLp.equiv 2 (κ → ℝ)).symm (fun j => x (i,j))
  left_inv x := by ext i j; rfl
  right_inv x := by ext p; rfl
  map_add' x y := by ext p; rfl
  map_smul' a x := by ext p; rfl

@[simp] theorem blockJoin_apply (x : ι → EuclideanSpace ℝ κ) (i : ι) (j : κ) :
    blockJoin x (i,j) = x i j := rfl

@[simp] theorem blockJoin_symm_apply (x : EuclideanSpace ℝ (ι × κ)) (i : ι) (j : κ) :
    blockJoin.symm x i j = x (i,j) := rfl

def blockJoinMeasurable : (ι → EuclideanSpace ℝ κ) ≃ᵐ EuclideanSpace ℝ (ι × κ) :=
  (blockJoin : (ι → EuclideanSpace ℝ κ) ≃ₗ[ℝ] EuclideanSpace ℝ (ι × κ)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

@[simp] theorem blockJoinMeasurable_apply (x : ι → EuclideanSpace ℝ κ) :
    blockJoinMeasurable x = blockJoin x := rfl

theorem uncurry_measurePreserving :
    MeasurePreserving (fun x : ι → κ → ℝ => fun p : ι × κ => x p.1 p.2) := by
  have hm : Measurable (fun x : ι → κ → ℝ => fun p : ι × κ => x p.1 p.2) :=
    measurable_pi_lambda _ (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
  refine ⟨hm, ?_⟩
  rw [volume_pi]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun x : ι → κ → ℝ => fun p : ι × κ => x p.1 p.2) ⁻¹' univ.pi s =
      univ.pi (fun i => univ.pi (fun j => s (i,j))) := by
    ext x
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, Prod.forall]
  rw [he, Measure.pi_pi]
  simp_rw [volume_pi_pi]
  rw [Fintype.prod_prod_type]

theorem blockJoin_measurePreserving : MeasurePreserving
    (blockJoin : (ι → EuclideanSpace ℝ κ) → EuclideanSpace ℝ (ι × κ)) := by
  have hp := volume_preserving_pi (fun _ : ι =>
    (PiLp.volume_preserving_equiv (ι := κ)))
  simpa only [Function.comp_def] using (PiLp.volume_preserving_equiv_symm (ι := ι × κ)).comp
    (uncurry_measurePreserving.comp hp)

theorem blockJoin_norm_sq (x : ι → EuclideanSpace ℝ κ) :
    ‖blockJoin x‖^2 = ∑ i, ‖x i‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  simpa only [blockJoin_apply] using Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => (PiLp.norm_sq_eq_of_L2 _ (x i)).symm)

theorem blockJoin_inner (x y : ι → EuclideanSpace ℝ κ) :
    ⟪blockJoin x,blockJoin y⟫_ℝ = ∑ i, ⟪x i,y i⟫_ℝ := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, blockJoin_apply]

/-- The full product of the integer modules, with the Euclidean product metric. -/
def productLattice (L : ι → Submodule ℤ (EuclideanSpace ℝ κ)) :
    Submodule ℤ (EuclideanSpace ℝ (ι × κ)) :=
  (Submodule.pi univ L).map (blockJoin.restrictScalars ℤ).toLinearMap

theorem blockJoin_mem_productLattice (L : ι → Submodule ℤ (EuclideanSpace ℝ κ))
    (x : ι → EuclideanSpace ℝ κ) :
    blockJoin x ∈ productLattice L ↔ ∀ i, x i ∈ L i := by
  rw [productLattice, Submodule.mem_map]
  constructor
  · rintro ⟨y,hy,hxy⟩
    have he : y=x := blockJoin.injective hxy
    subst y
    simpa only [Submodule.mem_pi, mem_univ, forall_true_left] using hy
  · intro hx
    exact ⟨x, by simpa only [Submodule.mem_pi, mem_univ, forall_true_left] using hx,rfl⟩

theorem blockJoin_mem_voronoi (L : ι → Submodule ℤ (EuclideanSpace ℝ κ))
    (x : ι → EuclideanSpace ℝ κ) :
    blockJoin x ∈ FacetGeometry.voronoi (productLattice L) ↔
      ∀ i, x i ∈ FacetGeometry.voronoi (L i) := by
  classical
  constructor
  · intro hx i
    rw [FacetGeometry.mem_voronoi_iff]
    intro z hz
    have h := (FacetGeometry.mem_voronoi_iff _ _).mp hx (blockJoin (Pi.single i z))
      ((blockJoin_mem_productLattice L _).mpr (by
        intro j
        by_cases hji : j=i
        · subst j; simpa using hz
        · simp [Pi.single_apply,hji]))
    rw [blockJoin_inner, blockJoin_norm_sq] at h
    simpa only [Pi.single_apply, apply_ite, ite_pow, inner_zero_right, norm_zero, zero_pow,
      OfNat.ofNat_ne_zero, show (0:ℝ)^2=0 by norm_num, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h
  · intro hx
    rw [FacetGeometry.mem_voronoi_iff]
    intro z hz
    obtain ⟨y,rfl⟩ := blockJoin.surjective z
    have hy := (blockJoin_mem_productLattice L y).mp hz
    rw [blockJoin_inner, blockJoin_norm_sq, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (FacetGeometry.mem_voronoi_iff _ _).mp (hx i) _ (hy i)

theorem product_voronoi (L : ι → Submodule ℤ (EuclideanSpace ℝ κ)) :
    FacetGeometry.voronoi (productLattice L) =
      blockJoin '' univ.pi (fun i => FacetGeometry.voronoi (L i)) := by
  ext p
  obtain ⟨x,rfl⟩ := blockJoin.surjective p
  rw [blockJoin_mem_voronoi]
  constructor
  · intro hx
    exact ⟨x,by simpa only [mem_pi,mem_univ,forall_true_left] using hx,rfl⟩
  · rintro ⟨y,hy,he⟩
    have hxy : y=x := blockJoin.injective he
    subst y
    simpa only [mem_pi,mem_univ,forall_true_left] using hy

end D4.Blocks
