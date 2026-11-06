import D4.Continuity

/-! Uniform finite sets of lattice competitors near a positive-definite form. -/
noncomputable section
open Matrix Set
namespace D4.Analytic
attribute [local instance] Matrix.normedAddCommGroup

theorem nearby_quadratic_coercive {Q : Gram} (hQ : Q.PosDef) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ∀ R : Gram, ‖R-Q‖ < ε → ∀ y : Vec, c * ‖y‖^2 ≤ quadratic R y := by
  obtain ⟨c, hc, hbound⟩ := quadratic_coercive hQ
  refine ⟨c/32, c/2, by positivity, by positivity, ?_⟩
  intro R hR y
  have hd := (abs_le.mp (abs_quadratic_le (R-Q) y)).1
  rw [quadratic_sub_matrix] at hd
  have he : 16 * ‖R-Q‖ ≤ c/2 := by linarith
  have hm := mul_le_mul_of_nonneg_right he (sq_nonneg ‖y‖)
  have hb := hbound y
  nlinarith only [hd, hm, hb]

/-- The finite set is uniform in both the form and the point. -/
theorem uniform_finite_competitors {Q : Gram} (hQ : Q.PosDef) (B E : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ s : Finset IntVec,
      ∀ R : Gram, ‖R-Q‖ < ε → ∀ x : Vec, ‖x‖ ≤ B →
        ∀ z : IntVec, quadratic R (x-castVec z) ≤ E → z ∈ s := by
  obtain ⟨ε, c, hε, hc, hbound⟩ := nearby_quadratic_coercive hQ
  obtain ⟨N, hN⟩ := exists_nat_gt (B + |E|/c + 1)
  let s : Set IntVec := {z | ∀ i : Fin 4, z i ∈ Set.Icc (-(N:ℤ)) N}
  have hs : s.Finite := Set.Finite.pi' (fun _ : Fin 4 => Set.finite_Icc (-(N:ℤ)) N)
  refine ⟨ε, hε, hs.toFinset, ?_⟩
  intro R hR x hx z hz
  apply hs.mem_toFinset.mpr
  intro i
  have hsq : ‖x-castVec z‖^2 ≤ |E|/c := by
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using (hbound R hR (x-castVec z)).trans (hz.trans (le_abs_self E))
  have hdist : ‖x-castVec z‖ ≤ |E|/c + 1 := by
    nlinarith only [hsq, sq_nonneg (‖x-castVec z‖-1/2)]
  have hnorm : ‖castVec z‖ ≤ B + |E|/c + 1 := by
    calc
      ‖castVec z‖ = ‖x-(x-castVec z)‖ := by congr 1; abel
      _ ≤ ‖x‖ + ‖x-castVec z‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hcoord : |(z i:ℝ)| ≤ (N:ℝ) := by
    have hh : |(z i:ℝ)| ≤ ‖castVec z‖ := by
      simpa only [castVec, Real.norm_eq_abs] using norm_le_pi_norm (castVec z) i
    linarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp hcoord
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

/-- Every actual nearest site in a bounded neighborhood belongs to a common
finite set, for all nearby positive-definite forms. -/
theorem uniform_finite_nearest_sites {Q : Gram} (hQ : Q.PosDef)
    (B : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ s : Finset IntVec,
      ∀ R : Gram, R.PosDef → ‖R-Q‖ < ε → ∀ x : Vec, ‖x‖ ≤ B →
        (∀ z : IntVec, quadratic R (x-castVec z) = nearest R x → z ∈ s) ∧
        ∃ z ∈ s, nearest R x = quadratic R (x-castVec z) := by
  obtain ⟨ε, hε, s, hs⟩ := uniform_finite_competitors hQ B (16*(‖Q‖+1)*B^2)
  refine ⟨min ε 1, lt_min hε zero_lt_one, s, ?_⟩
  intro R hR hclose x hx
  have he : ‖R-Q‖ < ε := hclose.trans_le (min_le_left _ _)
  have hnR : ‖R‖ ≤ ‖Q‖+1 := by
    have hd : ‖R-Q‖ < 1 := hclose.trans_le (min_le_right _ _)
    calc
      ‖R‖ = ‖(R-Q)+Q‖ := by congr 1; abel
      _ ≤ ‖R-Q‖ + ‖Q‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have henergy : nearest R x ≤ 16*(‖Q‖+1)*B^2 := by
    calc
      nearest R x ≤ quadratic R x := nearest_le_quadratic hR.posSemidef x
      _ ≤ |quadratic R x| := le_abs_self _
      _ ≤ 16*‖R‖*‖x‖^2 := abs_quadratic_le _ _
      _ ≤ 16*(‖Q‖+1)*B^2 := by gcongr
  have hall (z : IntVec) (hz : quadratic R (x-castVec z) = nearest R x) : z ∈ s :=
    hs R he x hx z (hz.le.trans henergy)
  refine ⟨hall, ?_⟩
  obtain ⟨z, hz⟩ := nearest_attained hR x
  exact ⟨z, hall z hz.symm, hz⟩

end D4.Analytic
