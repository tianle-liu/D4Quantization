import D4.C23LocalWindow
import D4.LocalWindowNeighborhood

noncomputable section
namespace D4.C23Local
open Set Filter Topology Analytic AreaEnvelope

/-- A compact zero face has arbitrarily thin genuine four-dimensional windows
inside every open neighborhood, uniformly under nearby continuous parameters. -/
theorem small_windows_eventually {X : Type*} [TopologicalSpace X]
    (P : X → WindowCoordinates → Vec)
    (hP : Continuous (fun p : X×WindowCoordinates => P p.1 p.2))
    (d : Plane → ℝ) (hd : Continuous d) (hn : ∀ L,0≤d L)
    (hc : IsCompact {L | d L≤1}) (x₀ : X) (O : Set Vec) (hO : IsOpen O)
    (hzero : ∀ L,d L=0 → P x₀ (L,(0,0))∈O) :
    ∃ η R : ℝ,0<η ∧ 0<R ∧ η<R/4 ∧
      ∀ᶠ x in 𝓝 x₀,P x '' referenceWindow {L | d L≤η} R⊆O := by
  let g : WindowCoordinates → ℝ := fun p => d p.1+|p.2.1|+|p.2.2|
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hgn (p : WindowCoordinates) : 0≤g p := by
    have h := hn p.1
    dsimp [g]
    positivity
  have hgc : IsCompact {p | g p≤1} := by
    apply (hc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset
      (isClosed_le hg continuous_const)
    intro p hp
    change d p.1+|p.2.1|+|p.2.2|≤1 at hp
    have hd0 := hn p.1
    have hx := abs_nonneg p.2.1
    have hy := abs_nonneg p.2.2
    refine ⟨?_,?_,?_⟩
    · change d p.1≤1; linarith
    · exact abs_le.mp (show |p.2.1|≤1 by linarith)
    · exact abs_le.mp (show |p.2.2|≤1 by linarith)
  have hpcont : Continuous (P x₀) := hP.comp (continuous_const.prodMk continuous_id)
  have hz : {p | g p=0}⊆(P x₀) ⁻¹' O := by
    intro p hp
    have hd0 := hn p.1
    have hx := abs_nonneg p.2.1
    have hy := abs_nonneg p.2.2
    change d p.1+|p.2.1|+|p.2.2|=0 at hp
    have hd' : d p.1=0 := by linarith
    have hx' : p.2.1=0 := abs_eq_zero.mp (by linarith)
    have hy' : p.2.2=0 := abs_eq_zero.mp (by linarith)
    have he : p=(p.1,(0,0)) := by ext <;> simp [hx',hy']
    change P x₀ p∈O
    rw [he]
    exact hzero p.1 hd'
  obtain ⟨σ,hσ,hσ1,hσO⟩ := positive_sublevel_subset g hg hgn hgc
    ((P x₀) ⁻¹' O) (hO.preimage hpcont) hz
  let R := σ/4
  let η := σ/32
  have hR : 0<R := by dsimp [R]; positivity
  have hη : 0<η := by dsimp [η]; positivity
  have hηR : η<R/4 := by dsimp [η,R]; linarith
  have hη1 : η≤1 := by dsimp [η]; linarith
  have hK : IsCompact (referenceWindow {L | d L≤η} R) := by
    apply IsCompact.prod _ (isCompact_Icc.prod isCompact_Icc)
    exact hc.of_isClosed_subset (isClosed_le hd continuous_const)
      (fun _ h => h.trans hη1)
  refine ⟨η,R,hη,hR,hηR,?_⟩
  apply compact_image_eventually_subset (fun p : X×WindowCoordinates => P p.1 p.2)
    hP x₀ (referenceWindow {L | d L≤η} R) hK O hO
  intro p hp
  apply hσO
  have hx : |p.2.1|≤R := abs_le.mpr hp.2.1
  have hy : |p.2.2|≤R := abs_le.mpr hp.2.2
  have hd' : d p.1≤η := hp.1
  change g p≤σ
  dsimp [g,η,R] at *
  linarith

end D4.C23Local
