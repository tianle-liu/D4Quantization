import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

/-!
# The moment perspective and its finite Jensen inequality

These are inequalities for the actual real-power functions in the
paper, proved from convexity of real powers. No geometric moment formula
is assumed in this module.
-/
noncomputable section
namespace D4.ConePerspective
open Finset Set

def powerPerspective (p v j : ℝ) : ℝ := j * (v / j) ^ p

def momentPerspective (d v j : ℝ) : ℝ :=
  d ^ (d / 2) * powerPerspective (1 + d / 2) v j

/-- The normalized moment as a function of a positive volume and moment. -/
def normalizedMoment (d v j : ℝ) : ℝ := j / (d * v ^ (1+2/d))

/-- Weighted Jensen for the perspective. The weights need not sum to one. -/
theorem powerPerspective_weighted {ι : Type*} (s : Finset ι)
    (p : ℝ) (hp : 1 ≤ p) (w v j : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (hj : ∀ i ∈ s, 0 < j i) (hJ : 0 < ∑ i ∈ s, w i * j i) :
    powerPerspective p (∑ i ∈ s, w i * v i) (∑ i ∈ s, w i * j i) ≤
      ∑ i ∈ s, w i * powerPerspective p (v i) (j i) := by
  let J := ∑ i ∈ s, w i * j i
  have hJ' : 0 < J := hJ
  have hsum : ∑ i ∈ s, w i * j i / J = 1 := by
    rw [← Finset.sum_div]
    exact div_self hJ'.ne'
  have hmean : (∑ i ∈ s, (w i * j i / J) * (v i / j i)) =
      (∑ i ∈ s, w i * v i) / J := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [(hj i hi).ne']
    ring
  have H := (convexOn_rpow hp).map_sum_le
    (fun i hi => div_nonneg (mul_nonneg (hw i hi) (hj i hi).le) hJ'.le)
    hsum (fun i hi => show v i / j i ∈ Ici (0 : ℝ) from div_nonneg (hv i hi) (hj i hi).le)
  simp only [smul_eq_mul] at H
  rw [hmean] at H
  have H' := mul_le_mul_of_nonneg_left H hJ'.le
  change J * ((∑ i ∈ s, w i * v i) / J) ^ p ≤ _
  refine H'.trans_eq ?_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold powerPerspective
  field_simp [hJ'.ne']
  ring

/-- Homogeneity of degree one for every positive scale. -/
theorem powerPerspective_homogeneous (p v j c : ℝ) (hc : 0 < c) :
    powerPerspective p (c * v) (c * j) = c * powerPerspective p v j := by
  unfold powerPerspective
  rw [mul_div_mul_left _ _ hc.ne']
  ring

/-- The quotient presentation appearing in the article. -/
theorem momentPerspective_eq_quotient (d v j : ℝ) (hv : 0 ≤ v) (hj : 0 < j) :
    momentPerspective d v j = d ^ (d / 2) * v ^ (1 + d / 2) / j ^ (d / 2) := by
  unfold momentPerspective powerPerspective
  rw [Real.div_rpow hv hj.le, show 1+d/2 = d/2+1 by ring,
    Real.rpow_add_one hj.ne']
  field_simp [hj.ne', (Real.rpow_pos_of_pos hj (d/2)).ne']
  ring

theorem momentPerspective_weighted {ι : Type*} (s : Finset ι)
    (d : ℝ) (hd : 0 ≤ d) (w v j : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (hj : ∀ i ∈ s, 0 < j i) (hJ : 0 < ∑ i ∈ s, w i * j i) :
    momentPerspective d (∑ i ∈ s, w i * v i) (∑ i ∈ s, w i * j i) ≤
      ∑ i ∈ s, w i * momentPerspective d (v i) (j i) := by
  have H := powerPerspective_weighted s (1+d/2) (by linarith) w v j hw hv hj hJ
  have H' := mul_le_mul_of_nonneg_left H (Real.rpow_nonneg hd (d/2))
  simpa only [momentPerspective, Finset.mul_sum, mul_left_comm] using H'

/-- The finite subadditivity needed when a body is split into pieces. -/
theorem momentPerspective_sum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (d : ℝ) (hd : 0 ≤ d) (v j : ι → ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hj : ∀ i ∈ s, 0 < j i) :
    momentPerspective d (∑ i ∈ s, v i) (∑ i ∈ s, j i) ≤
      ∑ i ∈ s, momentPerspective d (v i) (j i) := by
  simpa only [one_mul] using momentPerspective_weighted s d hd (fun _ => 1) v j
    (by intros; norm_num) hv hj (by
      simpa only [one_mul] using Finset.sum_pos (fun i hi => hj i hi) hs)

/-- Convexity of the power perspective on the positive quadrant. -/
theorem powerPerspective_convex (p : ℝ) (hp : 1 ≤ p) :
    ConvexOn ℝ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))
      (fun q : ℝ × ℝ => powerPerspective p q.1 q.2) := by
  refine ⟨(convex_Ioi (0:ℝ)).prod (convex_Ioi (0:ℝ)), ?_⟩
  intro x hx y hy a b ha hb hab
  have hJ : 0 < a * x.2 + b * y.2 := by
    exact (convex_Ioi (0:ℝ)) hx.2 hy.2 ha hb hab
  have H := powerPerspective_weighted (Finset.univ : Finset (Fin 2)) p hp
    ![a,b] ![x.1,y.1] ![x.2,y.2]
    (by intro i hi; fin_cases i; exact ha; exact hb)
    (by intro i hi; fin_cases i; exact hx.1.le; exact hy.1.le)
    (by intro i hi; fin_cases i <;> simp_all)
    (by simpa [Fin.sum_univ_succ] using hJ)
  simpa [Fin.sum_univ_succ, smul_eq_mul] using H

theorem momentPerspective_convex (d : ℝ) (hd : 0 ≤ d) :
    ConvexOn ℝ (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))
      (fun q : ℝ × ℝ => momentPerspective d q.1 q.2) := by
  simpa only [momentPerspective, smul_eq_mul] using
    (powerPerspective_convex (1+d/2) (by linarith)).smul (Real.rpow_nonneg hd (d/2))

/-- Exact conversion between the moment perspective and normalization. -/
theorem momentPerspective_eq_normalized (d v j : ℝ)
    (hd : 0 < d) (hv : 0 < v) (hj : 0 < j) :
    momentPerspective d v j = normalizedMoment d v j ^ (-d/2) := by
  have hg : 0 < normalizedMoment d v j := by
    unfold normalizedMoment
    positivity
  have hexp : (1+2/d)*(d/2) = 1+d/2 := by field_simp; ring
  rw [show -d/2 = -(d/2) by ring, Real.rpow_neg hg.le,
    ← Real.inv_rpow hg.le]
  unfold normalizedMoment
  rw [inv_div, Real.div_rpow (by positivity) hj.le,
    Real.mul_rpow hd.le (Real.rpow_nonneg hv.le _),
    ← Real.rpow_mul hv.le, hexp]
  exact momentPerspective_eq_quotient d v j hv.le hj

/-- A common moment-to-volume ratio cancels one homogeneous power. -/
theorem momentPerspective_of_ratio (d v c : ℝ) (hv : 0 < v) (hc : 0 < c) :
    momentPerspective d v (c*v) = d^(d/2) * v / c^(d/2) := by
  rw [momentPerspective_eq_quotient d v (c*v) hv.le (mul_pos hc hv),
    Real.mul_rpow hc.le hv.le, Real.rpow_add hv, Real.rpow_one]
  field_simp [(Real.rpow_pos_of_pos hc (d/2)).ne',
    (Real.rpow_pos_of_pos hv (d/2)).ne']
  ring

end D4.ConePerspective
