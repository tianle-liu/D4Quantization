import D4.NearestJointContinuity

noncomputable section
open Matrix Set
namespace D4.Analytic
attribute [local instance] Matrix.normedAddCommGroup

private theorem compact_finite_positive_bound {ι : Type*} (s : Finset ι)
    (K : Set Vec) (hK : IsCompact K) (f : ι → Vec → ℝ)
    (hf : ∀ i ∈ s, ContinuousOn (f i) K)
    (hpos : ∀ i ∈ s, ∀ x ∈ K, 0 < f i x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, ∀ x ∈ K, δ ≤ f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨δ, hδ, hb⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hpos j (Finset.mem_insert_of_mem hj))
    obtain ⟨η, hη, hc⟩ := hK.exists_forall_le'
      (hf i (Finset.mem_insert_self _ _)) (hpos i (Finset.mem_insert_self _ _))
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro j hj x hx
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (min_le_right _ _).trans (hc x hx)
    · exact (min_le_left _ _).trans (hb j hj x hx)

/-- A finite list containing every closest site on a compact set leaves a
uniform positive gap to every omitted integer site. -/
theorem compact_nearest_site_gap {Q : Gram} (hQ : Q.PosDef)
    (K : Set Vec) (hK : IsCompact K) (sites : Finset IntVec)
    (hsites : ∀ x ∈ K, ∀ z : IntVec,
      quadratic Q (x-castVec z) = nearest Q x → z ∈ sites) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ z : IntVec, z ∉ sites →
      nearest Q x + δ ≤ quadratic Q (x-castVec z) := by
  classical
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  let E : ℝ := 16*‖Q‖*B^2
  have henergy (x : Vec) (hx : x ∈ K) : nearest Q x ≤ E := by
    calc
      nearest Q x ≤ quadratic Q x := nearest_le_quadratic hQ.posSemidef x
      _ ≤ |quadratic Q x| := le_abs_self _
      _ ≤ 16*‖Q‖*‖x‖^2 := abs_quadratic_le _ _
      _ ≤ E := by dsimp [E]; gcongr; exact hB x hx
  obtain ⟨ε,hε,s,hs⟩ := uniform_finite_competitors hQ B (E+1)
  have hQclose : ‖Q-Q‖ < ε := by simpa using hε
  let f (z : IntVec) (x : Vec) : ℝ := quadratic Q (x-castVec z)-nearest Q x
  have hf (z : IntVec) : Continuous (f z) :=
    ((quadratic_continuous Q).comp (continuous_id.sub continuous_const)).sub
      (nearest_continuous_point hQ)
  have hp (z : IntVec) (hz : z ∈ s \ sites) (x : Vec) (hx : x ∈ K) : 0 < f z x := by
    have hn := nearest_le hQ.posSemidef x z
    have hne : quadratic Q (x-castVec z) ≠ nearest Q x := by
      intro he
      exact (Finset.mem_sdiff.mp hz).2 (hsites x hx z he)
    exact sub_pos.mpr (lt_of_le_of_ne hn (Ne.symm hne))
  obtain ⟨δ,hδ,hgap⟩ := compact_finite_positive_bound (s \ sites) K hK f
    (fun z _ => (hf z).continuousOn) hp
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro x hx z hz
  by_cases hzs : z ∈ s
  · have hh := hgap z (Finset.mem_sdiff.mpr ⟨hzs,hz⟩) x hx
    dsimp [f] at hh
    have hm : min δ 1 ≤ δ := min_le_left _ _
    linarith
  · have hh : E+1 < quadratic Q (x-castVec z) := by
      by_contra! hh
      exact hzs (hs Q hQclose x (hB x hx) z hh)
    have hn := henergy x hx
    have hm : min δ 1 ≤ 1 := min_le_right _ _
    linarith

end D4.Analytic
