import D4.NearestGap
import Mathlib.Topology.Compactness.Compact

noncomputable section
open Matrix Set Filter
open scoped Topology
namespace D4.Analytic
attribute [local instance] Matrix.normedAddCommGroup

/-- The gap to omitted lattice sites persists uniformly near the whole compact
set and under small positive-definite perturbations of the form. -/
theorem compact_nearest_gap_eventually {Q : Gram} (hQ : Q.PosDef)
    (K : Set Vec) (hK : IsCompact K) (sites : Finset IntVec)
    (hsites : ∀ x ∈ K, ∀ z : IntVec,
      quadratic Q (x-castVec z) = nearest Q x → z ∈ sites) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ p : Gram × Vec in (𝓝[{R : Gram | R.PosDef}] Q) ×ˢ (𝓝ˢ K),
        ∀ z : IntVec, z ∉ sites →
          nearest p.1 p.2 + δ ≤ quadratic p.1 (p.2-castVec z) := by
  classical
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let E : ℝ := 16*(‖Q‖+1)*(B+1)^2
  obtain ⟨ε,hε,s,hs⟩ := uniform_finite_competitors hQ (B+1) (E+1)
  obtain ⟨δ,hδ,hgap⟩ := compact_nearest_site_gap hQ K hK sites hsites
  let η := min (δ/2) 1
  have hη : 0 < η := lt_min (by positivity) zero_lt_one
  have hfinite : ∀ᶠ p : Gram × Vec in
      (𝓝[{R : Gram | R.PosDef}] Q) ×ˢ (𝓝ˢ K),
      ∀ z ∈ s \ sites, δ/2 < quadratic p.1 (p.2-castVec z)-nearest p.1 p.2 := by
    apply hK.mem_prod_nhdsSet_of_forall
    intro x hx
    have he : ∀ᶠ p : Gram × Vec in
        𝓝[({R : Gram | R.PosDef} ×ˢ (Set.univ : Set Vec))] (Q,x),
        ∀ z ∈ s \ sites, δ/2 < quadratic p.1 (p.2-castVec z)-nearest p.1 p.2 := by
      rw [Filter.eventually_all_finset]
      intro z hz
      have hcont : ContinuousWithinAt
          (fun p : Gram × Vec => quadratic p.1 (p.2-castVec z)-nearest p.1 p.2)
          ({R : Gram | R.PosDef} ×ˢ (Set.univ : Set Vec)) (Q,x) := by
        apply ContinuousWithinAt.sub
        · have hc : Continuous (fun p : Gram × Vec => quadratic p.1 (p.2-castVec z)) := by
            unfold quadratic dotProduct Matrix.mulVec
            fun_prop
          exact hc.continuousAt.continuousWithinAt
        · exact (nearest_joint_continuousOn (Q,x) hQ).mono (by intro p hp; exact hp.1)
      apply hcont.eventually (eventually_gt_nhds ?_)
      have hg := hgap x hx z (Finset.mem_sdiff.mp hz).2
      dsimp
      linarith
    simpa only [nhdsWithin_prod_eq, nhdsWithin_univ] using he
  have hRnear : {R : Gram | R.PosDef ∧ ‖R-Q‖ < min ε 1} ∈
      𝓝[{R : Gram | R.PosDef}] Q := by
    apply inter_mem self_mem_nhdsWithin
    apply nhdsWithin_le_nhds
    apply IsOpen.mem_nhds
    · exact isOpen_lt (show Continuous (fun R : Gram => ‖R-Q‖) by fun_prop) continuous_const
    · change ‖Q-Q‖ < min ε 1
      simpa only [sub_self, norm_zero] using lt_min hε zero_lt_one
  have hxnear : {x : Vec | ‖x‖ < B+1} ∈ 𝓝ˢ K := by
    have ho : IsOpen {x : Vec | ‖x‖ < B+1} :=
      isOpen_lt continuous_norm continuous_const
    apply ho.mem_nhdsSet.mpr
    intro x hx
    have := hB x hx
    dsimp
    linarith
  refine ⟨η,hη,?_⟩
  filter_upwards [hfinite, Filter.prod_mem_prod hRnear hxnear] with p hp hn
  intro z hz
  have hR : p.1.PosDef := hn.1.1
  have hnorm : ‖p.2‖ ≤ B+1 := hn.2.le
  have hclose : ‖p.1-Q‖ < ε := hn.1.2.trans_le (min_le_left _ _)
  by_cases hzs : z ∈ s
  · have hh := hp z (Finset.mem_sdiff.mpr ⟨hzs,hz⟩)
    have hm : η ≤ δ/2 := min_le_left _ _
    linarith
  · have hhigh : E+1 < quadratic p.1 (p.2-castVec z) := by
      apply lt_of_not_ge
      intro hsmall
      exact hzs (hs p.1 hclose p.2 hnorm z hsmall)
    have hRnorm : ‖p.1‖ ≤ ‖Q‖+1 := by
      have hh := hn.1.2.trans_le (min_le_right ε 1)
      calc
        ‖p.1‖ = ‖(p.1-Q)+Q‖ := by congr 1; abel
        _ ≤ ‖p.1-Q‖+‖Q‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have henergy : nearest p.1 p.2 ≤ E := by
      calc
        nearest p.1 p.2 ≤ quadratic p.1 p.2 := nearest_le_quadratic hR.posSemidef p.2
        _ ≤ |quadratic p.1 p.2| := le_abs_self _
        _ ≤ 16*‖p.1‖*‖p.2‖^2 := abs_quadratic_le _ _
        _ ≤ E := by dsimp [E]; gcongr
    have hm : η ≤ 1 := min_le_right _ _
    linarith

private theorem extract_product_neighborhood (Q : Gram) (K : Set Vec)
    (P : Gram × Vec → Prop)
    (he : ∀ᶠ p : Gram × Vec in (𝓝[{R : Gram | R.PosDef}] Q) ×ˢ (𝓝ˢ K), P p) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set Vec, IsOpen U ∧ K ⊆ U ∧
      ∀ R : Gram, R.PosDef → ‖R-Q‖ < ε → ∀ x ∈ U, P (R,x) := by
  obtain ⟨A,hA,U,hU,hAU⟩ := Filter.mem_prod_iff.mp he
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhdsWithin_iff.mp hA
  obtain ⟨V,hV,hKV,hVU⟩ := mem_nhdsSet_iff_exists.mp hU
  refine ⟨ε,hε,V,hV,hKV,?_⟩
  intro R hR hclose x hx
  have hRA : R ∈ A := hball ⟨by simpa only [Metric.mem_ball, dist_eq_norm] using hclose, hR⟩
  exact hAU (show (R,x) ∈ A ×ˢ U from ⟨hRA,hVU hx⟩)

theorem compact_nearest_gap_neighborhood {Q : Gram} (hQ : Q.PosDef)
    (K : Set Vec) (hK : IsCompact K) (sites : Finset IntVec)
    (hsites : ∀ x ∈ K, ∀ z : IntVec,
      quadratic Q (x-castVec z) = nearest Q x → z ∈ sites) :
    ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧ ∃ U : Set Vec, IsOpen U ∧ K ⊆ U ∧
      ∀ R : Gram, R.PosDef → ‖R-Q‖ < ε → ∀ x ∈ U,
        ∀ z : IntVec, z ∉ sites → nearest R x + δ ≤ quadratic R (x-castVec z) := by
  obtain ⟨δ,hδ,he⟩ := compact_nearest_gap_eventually hQ K hK sites hsites
  obtain ⟨ε,hε,U,hU,hKU,hbound⟩ := extract_product_neighborhood Q K _ he
  exact ⟨δ,ε,hδ,hε,U,hU,hKU,hbound⟩

end D4.Analytic
