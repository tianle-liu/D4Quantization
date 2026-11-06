import D4.PrincipalGeometry
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Support functions of the principal zonotope

The support value is attained by explicitly choosing each segment endpoint.
Separation then turns all real support inequalities into actual membership.
-/
noncomputable section
open Matrix Set
namespace D4.Principal
open Analytic

def support (w : Fin 10 → ℝ) (x : Vec) : ℝ :=
  ∑ e, w e * |dotProduct x (cone1Vectors e)|

theorem zonotope_support_le {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e)
    {r : Vec} (hr : r ∈ zonotope w) (x : Vec) : dotProduct x r ≤ support w x := by
  obtain ⟨t, ht, rfl⟩ := hr
  rw [generatorMap_dot, support]
  apply Finset.sum_le_sum
  intro e _
  calc
    t e * dotProduct x (cone1Vectors e) ≤ |t e * dotProduct x (cone1Vectors e)| := le_abs_self _
    _ = |t e| * |dotProduct x (cone1Vectors e)| := abs_mul _ _
    _ ≤ w e * |dotProduct x (cone1Vectors e)| :=
      mul_le_mul_of_nonneg_right (abs_le.mpr ⟨ht.1 e, ht.2 e⟩) (abs_nonneg _)

theorem zonotope_support_attained {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e) (x : Vec) :
    ∃ r ∈ zonotope w, dotProduct x r = support w x := by
  let t : Fin 10 → ℝ := fun e => if 0 ≤ dotProduct x (cone1Vectors e) then w e else -w e
  have ht : t ∈ Icc (-w) w := by
    constructor <;> intro e <;> dsimp [t] <;> split_ifs <;> linarith [hw e]
  refine ⟨generatorMap t, ⟨t, ht, rfl⟩, ?_⟩
  rw [generatorMap_dot, support]
  apply Finset.sum_congr rfl
  intro e _
  dsimp [t]
  split_ifs with h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]
    ring

theorem dual_eq_dot (f : Vec →L[ℝ] ℝ) (x : Vec) :
    f x = dotProduct (fun i => f (fun j => if i = j then 1 else 0)) x := by
  change f.toLinearMap x = _
  rw [LinearMap.pi_apply_eq_sum_univ f.toLinearMap x]
  simp only [dotProduct, smul_eq_mul, ContinuousLinearMap.coe_coe]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A complete, proved support characterization, with no polytope library axiom. -/
theorem mem_zonotope_iff_support {w : Fin 10 → ℝ} (hw : ∀ e, 0 ≤ w e) (r : Vec) :
    r ∈ zonotope w ↔ ∀ x : Vec, dotProduct x r ≤ support w x := by
  constructor
  · exact fun hr x => zonotope_support_le hw hr x
  · intro hr
    by_contra hn
    obtain ⟨f, u, hfu, hur⟩ := geometric_hahn_banach_closed_point
      (zonotope_convex w) (zonotope_isCompact w).isClosed hn
    let x : Vec := fun i => f (fun j => if i = j then 1 else 0)
    obtain ⟨s, hs, hss⟩ := zonotope_support_attained hw x
    have hfr : f r ≤ support w x := by simpa only [dual_eq_dot f r] using hr x
    have hfs : f s = support w x := by simpa only [dual_eq_dot f s] using hss
    linarith [hfu s hs]

end D4.Principal
