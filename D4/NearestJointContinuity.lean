import D4.NearestUniform
import Mathlib.Topology.Order.Lattice

noncomputable section
open Matrix Set Filter
open scoped Topology
namespace D4.Analytic
attribute [local instance] Matrix.normedAddCommGroup

theorem nearest_eq_finset_inf {Q : Gram} (hQ : Q.PosDef) (x : Vec)
    (s : Finset IntVec) (hs : s.Nonempty)
    (hattain : ∃ z ∈ s, nearest Q x = quadratic Q (x-castVec z)) :
    nearest Q x = s.inf' hs (fun z => quadratic Q (x-castVec z)) := by
  apply le_antisymm
  · exact Finset.le_inf' hs _ (fun z _ => nearest_le hQ.posSemidef x z)
  · obtain ⟨z, hz, he⟩ := hattain
    exact Finset.inf'_le_of_le _ hz he.symm.le

/-- Joint continuity follows from a common finite minimum locally. -/
theorem nearest_joint_continuousOn :
    ContinuousOn (fun p : Gram × Vec => nearest p.1 p.2) {p | p.1.PosDef} := by
  rintro ⟨Q,x⟩ hQ
  obtain ⟨ε,hε,s,hs⟩ := uniform_finite_nearest_sites hQ (‖x‖+1)
  have hQclose : ‖Q-Q‖ < ε := by simpa using hε
  have hxbound : ‖x‖ ≤ ‖x‖+1 := by linarith
  have hsn : s.Nonempty := by
    obtain ⟨z,hz,_⟩ := (hs Q hQ hQclose x hxbound).2
    exact ⟨z,hz⟩
  let f : Gram × Vec → ℝ := fun p => s.inf' hsn
    (fun z => quadratic p.1 (p.2-castVec z))
  have hf : Continuous f := by
    apply Continuous.finset_inf'_apply hsn
    intro z _
    unfold quadratic dotProduct Matrix.mulVec
    fun_prop
  have heq (p : Gram × Vec) (hp : p.1.PosDef) (hpQ : ‖p.1-Q‖ < ε)
      (hpx : ‖p.2‖ ≤ ‖x‖+1) : nearest p.1 p.2 = f p :=
    nearest_eq_finset_inf hp p.2 s hsn (hs p.1 hp hpQ p.2 hpx).2
  have hnear : ∀ᶠ p : Gram × Vec in 𝓝 (Q,x),
      ‖p.1-Q‖ < ε ∧ ‖p.2‖ < ‖x‖+1 := by
    apply IsOpen.mem_nhds
    · exact (isOpen_lt (show Continuous (fun p : Gram × Vec => ‖p.1-Q‖) by
        fun_prop) continuous_const).inter
        (isOpen_lt (show Continuous (fun p : Gram × Vec => ‖p.2‖) by
          fun_prop) continuous_const)
    · exact ⟨hQclose, by linarith⟩
  apply hf.continuousAt.continuousWithinAt.congr_of_eventuallyEq _
    (heq (Q,x) hQ hQclose hxbound)
  filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with p hp hn
  exact heq p hp hn.1 hn.2.le

theorem nearest_continuous_point {Q : Gram} (hQ : Q.PosDef) :
    Continuous (nearest Q) := by
  have h := nearest_joint_continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => hQ)
  exact h

end D4.Analytic
