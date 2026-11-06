import D4.C23BoundaryNearest
import D4.DualPeriodMoment
import D4.NearestLocalization
import D4.LocalWindowNeighborhood

/-! The true all-lattice nearest-site gap persists in dual coordinates. -/
set_option maxHeartbeats 600000
noncomputable section
namespace D4.C23Local
open Matrix Set Filter Topology Analytic Principal AreaEnvelope
attribute [local instance] Matrix.normedAddCommGroup

theorem dualInverse_joint_continuousAt {Q : Gram} (hQ : Q.PosDef) (r : Vec) :
    ContinuousAt (fun p : Gram×Vec => dualInverse p.1 p.2) (Q,r) := by
  have hsm : Continuous (fun p : Gram×Vec => (2:ℝ) • p.1) :=
    continuous_const.smul continuous_fst
  have hinv : ContinuousAt (fun A : Gram => A⁻¹) ((2:ℝ) • Q) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (dualMatrix_det_ne_zero hQ)
  have hi : ContinuousAt (fun p : Gram×Vec => ((2:ℝ) • p.1)⁻¹) (Q,r) :=
    hinv.comp (f := fun p : Gram×Vec => (2:ℝ) • p.1) (x := (Q,r)) hsm.continuousAt
  exact (continuous_fst.matrix_mulVec continuous_snd).continuousAt.comp
    (hi.prodMk continuous_snd.continuousAt)

theorem compact_dual_nearest_gap {Q : Gram} (hQ : Q.PosDef)
    (F : Set Vec) (hF : IsCompact F) (hsub : F⊆dualRegion Q) (S : Finset IntVec)
    (hsites : ∀ r∈F,∀ n : IntVec,siteCost Q r n=0 → n∈S) :
    ∃ δ ε : ℝ,0<δ ∧ 0<ε ∧ ∃ U : Set Vec,IsOpen U ∧ F⊆U ∧
      ∀ R : Gram,R.PosDef → ‖R-Q‖<ε → ∀ r∈U,∀ n : IntVec,n∉S →
        dualNearest R r+δ≤quadratic R (dualInverse R r-castVec n) := by
  let K := dualInverse Q '' F
  have hK : IsCompact K := hF.image (Matrix.toLin' (((2:ℝ) • Q)⁻¹)).continuous_of_finiteDimensional
  have hKS : ∀ x∈K,∀ n : IntVec,
      quadratic Q (x-castVec n)=nearest Q x → n∈S := by
    intro x hx n hn
    obtain ⟨r,hr,hrx⟩ := hx
    have hdx : dualMap Q x=r := by rw [← hrx,dualMap_dualInverse hQ]
    have hv : ((2:ℝ) • Q)*ᵥx∈dualRegion Q := by
      change dualMap Q x∈dualRegion Q
      rw [hdx]
      exact hsub hr
    have hh := (dual_zero_cost_iff_nearest hQ x hv n).mpr hn
    change siteCost Q (dualMap Q x) n=0 at hh
    rw [hdx] at hh
    exact hsites r hr n hh
  obtain ⟨δ,ε,hδ,hε,V,hV,hKV,hbound⟩ := compact_nearest_gap_neighborhood hQ K hK S hKS
  have he : ∀ᶠ p : Gram×Vec in (𝓝 Q) ×ˢ (𝓝ˢ F),dualInverse p.1 p.2∈V := by
    apply hF.mem_prod_nhdsSet_of_forall
    intro r hr
    have hh := (dualInverse_joint_continuousAt hQ r)
      (hV.mem_nhds (hKV ⟨r,hr,rfl⟩))
    simpa only [nhds_prod_eq] using hh
  obtain ⟨A,hA,B,hB,hAB⟩ := Filter.mem_prod_iff.mp he
  obtain ⟨ε₁,hε₁,hball⟩ := Metric.mem_nhds_iff.mp hA
  obtain ⟨U,hU,hFU,hUB⟩ := mem_nhdsSet_iff_exists.mp hB
  refine ⟨δ,min ε ε₁,hδ,lt_min hε hε₁,U,hU,hFU,?_⟩
  intro R hR hclose r hr n hn
  have hc1 : ‖R-Q‖<ε₁ := hclose.trans_le (min_le_right ε ε₁)
  have hd1 : dist R Q<ε₁ := by rw [dist_eq_norm]; exact hc1
  have hRA : R∈A := hball hd1
  have hmem : (R,r)∈A ×ˢ B := ⟨hRA,hUB hr⟩
  have hv : dualInverse R r∈V := @hAB (R,r) hmem
  exact hbound R hR (hclose.trans_le (min_le_left _ _)) (dualInverse R r) hv n hn

theorem compact_dual_nearest_sites {Q : Gram} (hQ : Q.PosDef)
    (F : Set Vec) (hF : IsCompact F) (hsub : F⊆dualRegion Q) (S : Finset IntVec)
    (hsites : ∀ r∈F,∀ n : IntVec,siteCost Q r n=0 → n∈S) :
    ∃ ε : ℝ,0<ε ∧ ∃ U : Set Vec,IsOpen U ∧ F⊆U ∧
      ∀ R : Gram,R.PosDef → ‖R-Q‖<ε → ∀ r∈U,∀ n : IntVec,
        quadratic R (dualInverse R r-castVec n)=dualNearest R r → n∈S := by
  obtain ⟨δ,ε,hδ,hε,U,hU,hFU,hgap⟩ := compact_dual_nearest_gap hQ F hF hsub S hsites
  refine ⟨ε,hε,U,hU,hFU,?_⟩
  intro R hR hclose r hr n hn
  by_contra hnot
  have hh := hgap R hR hclose r hr n hnot
  rw [hn] at hh
  linarith

end D4.C23Local
