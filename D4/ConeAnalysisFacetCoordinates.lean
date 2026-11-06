import D4.ConeAnalysisCoordinates
import D4.VoronoiFacetGeometry
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual orthogonal coordinates at a Voronoi facet. -/
noncomputable section
namespace D4.ConeAnalysis
open D4.FacetGeometry
open MeasureTheory
open scoped InnerProductSpace

instance tangentBorelSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (z : E) : BorelSpace (tangent z) :=
  Subtype.borelSpace _

def unitNormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : E) : E := ‖z‖⁻¹ • z

theorem norm_unitNormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {z : E} (hz : z ≠ 0) : ‖unitNormal z‖ = 1 := by
  rw [unitNormal, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (norm_nonneg z)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

def unitJoinLinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : E) : WithLp 2 (tangent z × ℝ) →ₗ[ℝ] E where
  toFun p := (p.fst:E) + p.snd • unitNormal z
  map_add' x y := by
    simp only [WithLp.add_fst, WithLp.add_snd, Submodule.coe_add, add_smul]
    abel
  map_smul' r x := by
    simp only [WithLp.smul_fst, WithLp.smul_snd, Submodule.coe_smul,
      smul_add, smul_smul, smul_eq_mul, RingHom.id_apply]

theorem unitJoin_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {z : E} (hz : z ≠ 0) (p : WithLp 2 (tangent z × ℝ)) :
    ‖unitJoinLinear z p‖^2 = ‖p‖^2 := by
  have horth : ⟪(p.fst:E),unitNormal z⟫_ℝ = 0 := by
    rw [unitNormal, real_inner_smul_right, real_inner_comm]
    simp only [show ⟪z,(p.fst:E)⟫_ℝ = 0 from p.fst.property, mul_zero]
  change ‖(p.fst:E)+p.snd • unitNormal z‖^2 = _
  rw [norm_add_sq_real, norm_smul, norm_unitNormal hz, mul_one,
    real_inner_smul_right, horth, mul_zero, mul_zero, add_zero,
    WithLp.prod_norm_sq_eq_of_L2]
  rfl

theorem unitJoin_surjective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {z : E} (hz : z ≠ 0) : Function.Surjective (unitJoinLinear z) := by
  intro x
  let t := ⟪unitNormal z,x⟫_ℝ
  have hmem : x-t • unitNormal z ∈ tangent z := by
    rw [mem_tangent]
    dsimp [t, unitNormal]
    simp only [inner_sub_right, real_inner_smul_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr hz]
    ring
  refine ⟨(WithLp.equiv 2 (tangent z × ℝ)).symm (⟨x-t • unitNormal z,hmem⟩,t), ?_⟩
  change (x-t • unitNormal z)+t • unitNormal z = x
  exact sub_add_cancel _ _

def unitJoin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {z : E} (hz : z ≠ 0) : WithLp 2 (tangent z × ℝ) ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := unitJoinLinear z
      norm_map' := fun p => (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (unitJoin_norm_sq hz p) }
    (unitJoin_surjective hz)

@[simp] theorem unitJoin_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {z : E} (hz : z ≠ 0) (p : WithLp 2 (tangent z × ℝ)) :
    unitJoin hz p = (p.fst:E)+p.snd • unitNormal z := rfl

def unitJoinProduct {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {z : E} (hz : z ≠ 0) :
    tangent z × ℝ ≃ᵐ E := by
  borelize (WithLp 2 (tangent z × ℝ))
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (tangent z) ℝ).toHomeomorph.toMeasurableEquiv.symm.trans
    (unitJoin hz).toMeasurableEquiv

@[simp] theorem unitJoinProduct_apply {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {z : E} (hz : z ≠ 0) (p : tangent z × ℝ) :
    unitJoinProduct hz p = (p.1:E)+p.2 • unitNormal z := rfl

theorem unitJoinProduct_measurePreserving {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {z : E} (hz : z ≠ 0) :
    MeasurePreserving (unitJoinProduct hz)
      ((volume : Measure (tangent z)).prod volume) volume := by
  borelize (WithLp 2 (tangent z × ℝ))
  have H : MeasurePreserving
      (WithLp.prodContinuousLinearEquiv 2 ℝ (tangent z) ℝ).toHomeomorph.toMeasurableEquiv
      volume ((volume : Measure (tangent z)).prod volume) := prodLp_volume_preserving
  exact (unitJoin hz).measurePreserving.comp H.symm

theorem unitJoinProduct_norm_sq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {z : E} (hz : z ≠ 0) (p : tangent z × ℝ) :
    ‖unitJoinProduct hz p‖^2 = ‖p.1‖^2+p.2^2 := by
  have H := unitJoin_norm_sq hz ((WithLp.equiv 2 (tangent z × ℝ)).symm p)
  rw [WithLp.prod_norm_sq_eq_of_L2] at H
  simpa only [WithLp.equiv_symm_fst, WithLp.equiv_symm_snd, Real.norm_eq_abs, sq_abs] using H

theorem integral_unitJoinProduct_image {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {z : E} (hz : z ≠ 0)
    (S : Set (tangent z × ℝ)) (f : E → ℝ) :
    (∫ x in unitJoinProduct hz '' S, f x) =
      ∫ p in S, f ((p.1:E)+p.2 • unitNormal z)
        ∂((volume : Measure (tangent z)).prod volume) := by
  exact (unitJoinProduct_measurePreserving hz).setIntegral_image_emb
    (unitJoinProduct hz).measurableEmbedding f S

end D4.ConeAnalysis
