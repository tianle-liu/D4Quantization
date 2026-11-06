import D4.C23BoundaryHexagonData
import D4.NearestTorus

/-! Exact relation between zero dual site costs and true nearest lattice sites. -/
noncomputable section
namespace D4.C23Local
open Matrix Set Analytic Principal AreaEnvelope

theorem siteCost_dual_eq_distance_difference {Q : Gram} (hQ : Q.IsHermitian)
    (x : Vec) (n : IntVec) :
    siteCost Q (((2 : ℝ) • Q) *ᵥ x) n =
      quadratic Q (x-castVec n)-quadratic Q x := by
  rw [siteCost,Matrix.smul_mulVec_assoc,dotProduct_smul,smul_eq_mul,
    quadratic_sub_vec hQ,quadratic_pair_symmetric hQ (castVec n) x]
  ring

theorem dual_zero_cost_iff_nearest {Q : Gram} (hQ : Q.PosDef) (x : Vec)
    (hx : ((2 : ℝ) • Q) *ᵥ x ∈ dualRegion Q) (n : IntVec) :
    siteCost Q (((2 : ℝ) • Q) *ᵥ x) n=0 ↔
      quadratic Q (x-castVec n)=nearest Q x := by
  have hv : x∈voronoi Q := by
    rw [← dualRegion_preimage hQ.isHermitian]
    simpa only [Set.mem_preimage,zero_add] using hx
  rw [nearest_eq_quadratic_on_voronoi hQ.posSemidef hv,
    siteCost_dual_eq_distance_difference hQ.isHermitian,sub_eq_zero]

theorem dualSquareFace_compact {Q : Gram} (hQ : Q.PosDef) (i j : Fin 4) :
    IsCompact (dualSquareFace Q i j) := by
  have he : dualSquareFace Q i j = dualRegion Q ∩
      {r : Vec | r i=Q i i} ∩ {r : Vec | r j=Q j j} := by
    ext r; simp only [dualSquareFace,mem_setOf_eq,mem_inter_iff]; tauto
  rw [he]
  exact ((dualRegion_compact hQ).inter_right
    (isClosed_eq (continuous_apply i) continuous_const)).inter_right
    (isClosed_eq (continuous_apply j) continuous_const)

theorem dual_face_translate_injective {Q : Gram} (hQ : Q.PosDef)
    (F : Set Vec) (hF : F⊆dualRegion Q) (S : Finset IntVec)
    (hS : ∀ r∈F,∀ n∈S,siteCost Q r n=0)
    (hcount : ∀ r∈F,∃ T : Finset IntVec,
      (∀ n : IntVec,siteCost Q r n=0 → n∈T) ∧ T.card<2*S.card) :
    ∀ r∈F,∀ n : IntVec,r+((2:ℝ) • Q)*ᵥ(castVec n)∈F → n=0 := by
  let G : Set Vec := (fun x => ((2:ℝ) • Q)*ᵥx) ⁻¹' F
  have hcommon : ∀ x∈G,∀ n∈S,quadratic Q (x-castVec n)=nearest Q x := by
    intro x hx n hn
    exact (dual_zero_cost_iff_nearest hQ x (hF hx) n).mp (hS _ hx n hn)
  have hnumber : ∀ x∈G,∃ T : Finset IntVec,
      (∀ n : IntVec,quadratic Q (x-castVec n)=nearest Q x → n∈T) ∧
        T.card<2*S.card := by
    intro x hx
    obtain ⟨T,hT,hcard⟩ := hcount _ hx
    refine ⟨T,?_,hcard⟩
    intro n hn
    exact hT n ((dual_zero_cost_iff_nearest hQ x (hF hx) n).mpr hn)
  have hinj := nearest_face_translate_injective hQ G S hcommon hnumber
  intro r hr n hn
  obtain ⟨x,hx⟩ := (affineMeasurableEquiv ((2:ℝ) • Q)
    (dualRegion_det_pos hQ).ne' 0).surjective r
  change 0+((2:ℝ) • Q)*ᵥx=r at hx
  simp only [zero_add] at hx
  apply hinj x (by change ((2:ℝ) • Q)*ᵥx∈F; rwa [hx]) n
  change ((2:ℝ) • Q)*ᵥ(x+castVec n)∈F
  rwa [Matrix.mulVec_add,hx]

end D4.C23Local
