import D4.C23BoundaryGap
import D4.C23SmallWindows
import D4.DualEmbeddedNeighborhood

noncomputable section
namespace D4.C23Local
open Matrix Set Filter Topology Analytic Principal AreaEnvelope
attribute [local instance] Matrix.normedAddCommGroup

theorem windows_nearest_sites
    (P : Gram → WindowCoordinates → Vec)
    (hP : Continuous (fun p : Gram×WindowCoordinates => P p.1 p.2))
    (d : Plane → ℝ) (hd : Continuous d) (hn : ∀ L,0≤d L)
    (hc : IsCompact {L | d L≤1}) (Q₀ : Gram) (hQ₀ : Q₀.PosDef)
    (F : Set Vec) (hF : IsCompact F) (hsub : F⊆dualRegion Q₀) (S : Finset IntVec)
    (hsites : ∀ r∈F,∀ n : IntVec,siteCost Q₀ r n=0 → n∈S)
    (htorus : ∀ r∈F,∀ n : IntVec,r+dualMap Q₀ (castVec n)∈F → n=0)
    (hzero : ∀ L,d L=0 → P Q₀ (L,(0,0))∈F) :
    ∃ η R ε : ℝ,0<η ∧ 0<R ∧ η<R/4 ∧ 0<ε ∧
      ∀ Q : Gram,Q.PosDef → ‖Q-Q₀‖<ε →
        let W := P Q '' referenceWindow {L | d L≤η} R
        (∀ r∈W,∀ n : IntVec,
          quadratic Q (dualInverse Q r-castVec n)=dualNearest Q r → n∈S) ∧
        (∀ r∈W,∀ n : IntVec,r+dualMap Q (castVec n)∈W → n=0) := by
  obtain ⟨ε₀,hε₀,U,hU,hFU,hnear⟩ := compact_dual_nearest_sites hQ₀ F hF hsub S hsites
  obtain ⟨εe,hεe,E,hE,hFE,hembed⟩ := compact_dual_embedded_neighborhood hQ₀ F hF htorus
  obtain ⟨η,R,hη,hR,hηR,he⟩ := small_windows_eventually P hP d hd hn hc Q₀ (U∩E)
    (hU.inter hE) (fun L hL => ⟨hFU (hzero L hL),hFE (hzero L hL)⟩)
  obtain ⟨ε₁,hε₁,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨η,R,min ε₀ (min εe ε₁),hη,hR,hηR,lt_min hε₀ (lt_min hεe hε₁),?_⟩
  intro Q hQ hclose
  have hc0 : ‖Q-Q₀‖<ε₀ := hclose.trans_le (min_le_left _ _)
  have hce : ‖Q-Q₀‖<εe := hclose.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hc1 : ‖Q-Q₀‖<ε₁ := hclose.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hwin : P Q '' referenceWindow {L | d L≤η} R⊆U∩E :=
    hball (by simpa only [Metric.mem_ball,dist_eq_norm] using hc1)
  constructor
  · intro r hr n hn'
    exact hnear Q hQ hc0 r (hwin hr).1 n hn'
  · intro r hr n hn'
    exact hembed Q hce r (hwin hr).2 n (hwin hn').2

theorem windowPoint2_joint_continuous {U : Plane → ℝ} (hU : Continuous U) :
    Continuous (fun p : Gram×WindowCoordinates => windowPoint2 p.1 U p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [windowPoint2,inverseCoordinates2,fiberCoordinates,
    Fin.reduceFinMk,Matrix.cons_val] <;> fun_prop

theorem windowPoint3_joint_continuous {U : Plane → ℝ} (hU : Continuous U) :
    Continuous (fun p : Gram×WindowCoordinates => windowPoint3 p.1 U p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [windowPoint3,inverseCoordinates3,fiberCoordinates,
    Fin.reduceFinMk,Matrix.cons_val] <;> fun_prop


end D4.C23Local
