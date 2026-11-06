import D4.Definitions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Attainment of the nearest-lattice-point infimum

The infimum in the analytic definition ranges over all of ℤ⁴. Positive
definiteness provides a quadratic coercivity bound; every bounded-energy
set of integer competitors is therefore finite. A minimizer on one such
set is a global minimizer. This connects the analytic infimum to a genuine
nearest integer point without assuming a finite search bound as an axiom.
-/

noncomputable section
open Matrix Set
namespace D4.Analytic

theorem quadratic_smul_vec (Q : Gram) (r : ℝ) (x : Vec) :
    quadratic Q (r • x) = r^2 * quadratic Q x := by
  simp [quadratic, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Positive definite quadratic forms dominate a positive multiple of squared norm. -/
theorem quadratic_coercive {Q : Gram} (hQ : Q.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Vec, c * ‖x‖^2 ≤ quadratic Q x := by
  obtain ⟨c, hc, hbound⟩ :=
    (isCompact_sphere (0 : Vec) 1).exists_forall_le'
      (quadratic_continuous Q).continuousOn (a := 0) (by
        intro x hx
        have hn : ‖x‖ = 1 := by simpa [Metric.mem_sphere] using hx
        have hx0 : x ≠ 0 := by intro he; simp [he] at hn
        simpa [quadratic] using hQ.2 x hx0)
  refine ⟨c, hc, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx, quadratic]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy : c ≤ quadratic Q (‖x‖⁻¹ • x) := by
    apply hbound
    simpa [Metric.mem_sphere] using (norm_smul_inv_norm (𝕜 := ℝ) hx)
  calc
    c * ‖x‖^2 ≤ quadratic Q (‖x‖⁻¹ • x) * ‖x‖^2 :=
      mul_le_mul_of_nonneg_right hy (sq_nonneg _)
    _ = quadratic Q x := by rw [quadratic_smul_vec]; field_simp

/-- Every energy sublevel contains only finitely many integer competitors. -/
theorem finite_nearest_sublevel {Q : Gram} (hQ : Q.PosDef) (x : Vec) (E : ℝ) :
    {z : IntVec | quadratic Q (x - castVec z) ≤ E}.Finite := by
  by_cases hE : 0 ≤ E
  · obtain ⟨c, hc, hcoerce⟩ := quadratic_coercive hQ
    obtain ⟨N, hN⟩ := exists_nat_gt (‖x‖ + E/c + 1)
    apply (Set.Finite.pi' (fun _ : Fin 4 => Set.finite_Icc (-(N : ℤ)) (N : ℤ))).subset
    intro z hz i
    have hs : ‖x - castVec z‖^2 ≤ E/c := by
      apply (le_div_iff₀ hc).mpr
      simpa [mul_comm] using (hcoerce (x - castVec z)).trans hz
    have hd : ‖x - castVec z‖ ≤ E/c + 1 := by
      nlinarith only [hs, sq_nonneg (‖x - castVec z‖ - 1/2)]
    have hzNorm : ‖castVec z‖ ≤ ‖x‖ + (E/c + 1) := by
      calc
        ‖castVec z‖ = ‖x - (x - castVec z)‖ := by congr 1; abel
        _ ≤ ‖x‖ + ‖x - castVec z‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add_left hd _
    have hi : |(z i : ℝ)| ≤ (N : ℝ) := by
      have hcoord := norm_le_pi_norm (castVec z) i
      have hi' : |(z i : ℝ)| ≤ ‖castVec z‖ := by
        simpa [castVec, Real.norm_eq_abs] using hcoord
      linarith
    obtain ⟨hlo, hhi⟩ := abs_le.mp hi
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  · have hempty : {z : IntVec | quadratic Q (x - castVec z) ≤ E} = ∅ := by
      apply Set.eq_empty_of_forall_not_mem
      intro z hz
      exact hE ((quadratic_nonneg hQ.posSemidef _).trans hz)
    rw [hempty]
    exact Set.finite_empty

/-- A nearest integer point exists for every positive-definite form and every point. -/
theorem nearest_point_exists {Q : Gram} (hQ : Q.PosDef) (x : Vec) :
    ∃ z : IntVec, ∀ w : IntVec,
      quadratic Q (x - castVec z) ≤ quadratic Q (x - castVec w) := by
  let s : Set IntVec := {z | quadratic Q (x - castVec z) ≤ quadratic Q x}
  have hs : s.Finite := finite_nearest_sublevel hQ x (quadratic Q x)
  have hzero : (0 : IntVec) ∈ s := by simp [s, castVec, Pi.sub_def]
  obtain ⟨z, hz, hmin⟩ := Set.exists_min_image s
    (fun z => quadratic Q (x - castVec z)) hs ⟨0, hzero⟩
  refine ⟨z, ?_⟩
  intro w
  by_cases hw : w ∈ s
  · exact hmin w hw
  · exact hz.trans (le_of_lt (lt_of_not_ge hw))

/-- The infinite infimum in `nearest` equals the value at an actual integer point. -/
theorem nearest_attained {Q : Gram} (hQ : Q.PosDef) (x : Vec) :
    ∃ z : IntVec, nearest Q x = quadratic Q (x - castVec z) := by
  obtain ⟨z, hz⟩ := nearest_point_exists hQ x
  refine ⟨z, le_antisymm (nearest_le hQ.posSemidef x z) ?_⟩
  exact le_ciInf hz

/-- Zero nearest-point energy characterizes the integer lattice exactly. -/
theorem nearest_eq_zero_iff {Q : Gram} (hQ : Q.PosDef) (x : Vec) :
    nearest Q x = 0 ↔ ∃ z : IntVec, x = castVec z := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := nearest_attained hQ x
    refine ⟨z, ?_⟩
    by_contra hne
    have hpos : 0 < quadratic Q (x - castVec z) := by
      simpa [quadratic] using hQ.2 (x - castVec z) (sub_ne_zero.mpr hne)
    linarith
  · rintro ⟨z, rfl⟩
    exact nearest_at_integer hQ.posSemidef z

end D4.Analytic
