import D4.PrincipalIntegral

/-! Lebesgue integration on standard simplices, starting with Fubini. -/
noncomputable section
open Matrix MeasureTheory Set
namespace D4.Principal
open Analytic

def standardSimplex (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ r}

theorem standardSimplex_closed (n : ℕ) (r : ℝ) : IsClosed (standardSimplex n r) := by
  change IsClosed ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i ≤ r})
  simpa only [Set.setOf_forall] using
    (isClosed_iInter (fun i : Fin n => isClosed_le
      (continuous_const : Continuous (fun _ : Fin n → ℝ => (0 : ℝ))) (continuous_apply i))).inter
      (isClosed_le (show Continuous (fun x : Fin n → ℝ => ∑ i, x i) by fun_prop)
        (continuous_const : Continuous (fun _ : Fin n → ℝ => r)))

theorem standardSimplex_subset_box (n : ℕ) (r : ℝ) :
    standardSimplex n r ⊆ Icc 0 (fun _ => r) := by
  intro x hx
  refine ⟨hx.1, fun i => le_trans ?_ hx.2⟩
  exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)

theorem standardSimplex_compact (n : ℕ) (r : ℝ) : IsCompact (standardSimplex n r) :=
  isCompact_Icc.of_isClosed_subset (standardSimplex_closed n r) (standardSimplex_subset_box n r)

theorem mem_standardSimplex_cons (n : ℕ) (r t : ℝ) (y : Fin n → ℝ) :
    Fin.cons t y ∈ standardSimplex (n + 1) r ↔
      t ∈ Icc 0 r ∧ y ∈ standardSimplex n (r - t) := by
  simp only [standardSimplex, mem_setOf_eq, Fin.forall_fin_succ, Fin.cons_zero,
    Fin.cons_succ, Fin.sum_univ_succ, mem_Icc]
  constructor
  · rintro ⟨⟨ht, hy⟩, hs⟩
    have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hy i)
    exact ⟨⟨ht, by linarith⟩, hy, by linarith⟩
  · rintro ⟨⟨ht, _⟩, hy, hs⟩
    exact ⟨⟨ht, hy⟩, by linarith⟩

theorem standardSimplex_integral_succ (n : ℕ) (r : ℝ)
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Continuous f) :
    (∫ x in standardSimplex (n + 1) r, f x) =
      ∫ t in Icc 0 r, ∫ y in standardSimplex n (r - t), f (Fin.cons t y) := by
  classical
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have heval (p : ℝ × (Fin n → ℝ)) : e p = Fin.cons p.1 p.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero]
  let g := (standardSimplex (n + 1) r).indicator f
  have hg : Integrable g :=
    (integrable_indicator_iff (standardSimplex_closed (n + 1) r).measurableSet).mpr
      (hf.continuousOn.integrableOn_compact (standardSimplex_compact (n + 1) r))
  rw [← integral_indicator (standardSimplex_closed (n + 1) r).measurableSet]
  change (∫ x, g x) = _
  rw [← he.integral_comp' g]
  have hgcomp : Integrable (g ∘ e) :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr hg
  change (∫ p : ℝ × (Fin n → ℝ), (g ∘ e) p ∂volume.prod volume) = _
  rw [integral_prod _ hgcomp]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Icc 0 r
  · simp only [indicator_of_mem ht]
    rw [← integral_indicator (standardSimplex_closed n (r - t)).measurableSet]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [g, Function.comp_apply, heval, mem_standardSimplex_cons,
      indicator_apply, ht, true_and]
  · simp only [indicator_of_not_mem ht]
    apply integral_eq_zero_of_ae
    filter_upwards [] with y
    simp only [g, Function.comp_apply, heval, indicator_apply, mem_standardSimplex_cons,
      ht, false_and, ite_false, Pi.zero_apply]

end D4.Principal
