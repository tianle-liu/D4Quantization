import D4.ConePerspective
import Mathlib.Analysis.MeanInequalities

/-! The exact lower bound and equality condition for products of
orthogonal blocks, once their moments have been integrated. -/
noncomputable section
namespace D4.Blocks
open scoped BigOperators
open Finset
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def blockRatio (g a : ι → ℝ) : ℝ :=
  ((∑ i, g i * a i) / Fintype.card ι) /
    (∏ i, a i ^ (1 / (Fintype.card ι : ℝ)))

theorem blockRatio_lower_eq (g a : ι → ℝ) (b : ℝ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hg : ∀ i, b ≤ g i) :
    b ≤ blockRatio g a ∧
      (blockRatio g a = b ↔ (∀ i, g i = b) ∧ (∀ i j, a i = a j)) := by
  classical
  let k : ℝ := Fintype.card ι
  let A : ℝ := (∑ i, a i) / k
  let G : ℝ := ∏ i, a i ^ (1/k)
  let N : ℝ := (∑ i, g i * a i) / k
  have hk : 0 < k := by dsimp [k]; exact_mod_cast Fintype.card_pos
  have hw : ∑ i : ι, (1/k:ℝ) = 1 := by simp [k, ne_of_gt hk]
  have hG : 0 < G := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (ha i) _
  have hmean : G ≤ A := by
    have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : ι => 1/k) a
      (fun _ _ => (one_div_pos.mpr hk).le) hw (fun i _ => (ha i).le)
    simpa [G,A,div_eq_mul_inv,Finset.mul_sum,Finset.sum_mul,mul_comm] using h
  have hsum : b*A ≤ N := by
    dsimp [A,N]
    rw [← mul_div_assoc, Finset.mul_sum]
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hg i) (ha i).le) hk.le
  have hbn : b*G ≤ N := (mul_le_mul_of_nonneg_left hmean hb.le).trans hsum
  have hratio : blockRatio g a = N/G := rfl
  refine ⟨by rw [hratio]; exact (le_div_iff₀ hG).mpr hbn, ?_⟩
  constructor
  · intro h
    have hN : N = b*G := (div_eq_iff hG.ne').mp (hratio.symm.trans h)
    have hAG : A = G := by nlinarith
    have hNsum : (∑ i, g i * a i) = ∑ i, b * a i := by
      have hNA : N = b*A := by rw [hN,hAG]
      dsimp [N,A] at hNA
      apply (div_left_inj' hk.ne').mp
      simpa only [← Finset.mul_sum, mul_div_assoc] using hNA
    have hdiff : ∑ i, (g i-b)*a i = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, hNsum, sub_self]
    have hgeq : ∀ i, g i = b := by
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) => mul_nonneg (sub_nonneg.mpr (hg j)) (ha j).le)).mp hdiff i (Finset.mem_univ _)
      exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_right (ha i).ne')
    have hconst := (Real.geom_mean_eq_arith_mean_weighted_iff' Finset.univ
      (fun _ : ι => 1/k) a (fun _ _ => one_div_pos.mpr hk) hw (fun i _ => (ha i).le)).mp
      (by simpa [G,A,div_eq_mul_inv,Finset.mul_sum,Finset.sum_mul,mul_comm] using hAG.symm)
    exact ⟨hgeq, fun i j => (hconst i (Finset.mem_univ _)).trans (hconst j (Finset.mem_univ _)).symm⟩
  · rintro ⟨hg,haeq⟩
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hG' : G = a i := by
      dsimp [G]
      simp_rw [show ∀ j, a j = a i from fun j => haeq j i]
      rw [Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul (ha i).le]
      simp [k, hk.ne']
    have hN' : N = b * a i := by
      simp only [N, hg, show ∀ j, a j = a i from fun j => haeq j i, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      dsimp [k]
      field_simp
    rw [hratio,hN',hG',mul_div_cancel_right₀ _ (ha i).ne']

/-- The displayed product formula, with the original cell volumes. -/
def blockNormalizedMoment (d : ℝ) (g v : ι → ℝ) : ℝ :=
  ((∑ i, g i * (v i) ^ (2/d)) / Fintype.card ι) /
    ((∏ i, v i) ^ (2/((Fintype.card ι:ℝ)*d)))

theorem blockNormalizedMoment_eq_ratio (d : ℝ) (g v : ι → ℝ)
    (hv : ∀ i, 0 < v i) :
    blockNormalizedMoment d g v = blockRatio g (fun i => (v i)^(2/d)) := by
  unfold blockNormalizedMoment blockRatio
  congr 1
  rw [← Real.finset_prod_rpow _ _ (fun i _ => (hv i).le)]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_mul (hv i).le]
  congr 1
  ring

theorem blockNormalizedMoment_lower_eq (d : ℝ) (g v : ι → ℝ) (b : ℝ)
    (hd : 0 < d) (hv : ∀ i, 0 < v i) (hb : 0 < b) (hg : ∀ i, b ≤ g i) :
    b ≤ blockNormalizedMoment d g v ∧
      (blockNormalizedMoment d g v = b ↔
        (∀ i, g i = b) ∧ (∀ i j, v i = v j)) := by
  rw [blockNormalizedMoment_eq_ratio d g v hv]
  have h := blockRatio_lower_eq g (fun i => (v i)^(2/d)) b
    (fun i => Real.rpow_pos_of_pos (hv i) _) hb hg
  refine ⟨h.1, h.2.trans ?_⟩
  constructor
  · rintro ⟨hg,he⟩
    refine ⟨hg,fun i j => ?_⟩
    exact (Real.rpow_left_inj (hv i).le (hv j).le (ne_of_gt (div_pos (by norm_num) hd))).mp (he i j)
  · rintro ⟨hg,he⟩
    refine ⟨hg,fun i j => ?_⟩
    exact congrArg (fun t : ℝ => t^(2/d)) (he i j)

/-- Normalize the exact Fubini moment of a finite orthogonal product. -/
theorem normalizedMoment_product_formula [DecidableEq ι] (d : ℝ) (v j : ι → ℝ)
    (hd : 0 < d) (hv : ∀ i, 0 < v i) :
    ConePerspective.normalizedMoment ((Fintype.card ι:ℝ)*d)
      (∏ i, v i) (∑ i, j i * ∏ l ∈ Finset.univ.erase i, v l) =
    blockNormalizedMoment d (fun i => ConePerspective.normalizedMoment d (v i) (j i)) v := by
  classical
  let k : ℝ := Fintype.card ι
  let V : ℝ := ∏ i, v i
  have hk : 0 < k := by dsimp [k]; exact_mod_cast Fintype.card_pos
  have hV : 0 < V := Finset.prod_pos fun i _ => hv i
  have hterm (i : ι) :
      ConePerspective.normalizedMoment d (v i) (j i) * (v i)^(2/d) = j i / (d*v i) := by
    rw [ConePerspective.normalizedMoment, Real.rpow_add (hv i), Real.rpow_one]
    field_simp [hd.ne', (hv i).ne', (Real.rpow_pos_of_pos (hv i) (2/d)).ne']
    <;> ring
  have hsum : (∑ i, j i * ∏ l ∈ Finset.univ.erase i, v l) =
      d*V * ∑ i, ConePerspective.normalizedMoment d (v i) (j i) * (v i)^(2/d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hterm, show V = v i * ∏ l ∈ Finset.univ.erase i, v l from
      (Finset.mul_prod_erase Finset.univ v (Finset.mem_univ i)).symm]
    field_simp [hd.ne', (hv i).ne', (Real.rpow_pos_of_pos (hv i) (2/d)).ne']
    <;> ring
  rw [hsum]
  unfold ConePerspective.normalizedMoment blockNormalizedMoment
  change (d*V * _) / ((k*d)*V^(1+2/(k*d))) = (_/k)/V^(2/(k*d))
  rw [Real.rpow_add hV, Real.rpow_one]
  field_simp [hd.ne', hk.ne', hV.ne', (Real.rpow_pos_of_pos hV (2/(k*d))).ne']
  <;> ring

end D4.Blocks
