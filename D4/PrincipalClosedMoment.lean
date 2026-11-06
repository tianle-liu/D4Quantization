import D4.PrincipalTreeMomentIdentity

noncomputable section
namespace D4.Certificate

theorem eval_congr_bounded (p : Poly) (n : Nat) (x y : Nat → ℝ)
    (hp : ∀ t ∈ p, ∀ i ∈ t.1, i < n) (hxy : ∀ i < n, x i=y i) :
    eval x p = eval y p := by
  unfold eval
  congr 1
  apply List.map_congr_left
  intro t ht
  congr 1
  unfold monomial
  congr 1
  exact List.map_congr_left fun i hi => hxy i (hp t ht i hi)

end D4.Certificate
namespace D4.Principal
open Certificate CertificateMoments Analytic

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem momentC1_support : ∀ t ∈ momentC1, ∀ i ∈ t.1, i < 10 := by
  have hh : momentC1.all (fun t => t.1.all (fun i => decide (i < 10))) = true := by kernel_rfl
  simpa only [List.all_eq_true, decide_eq_true_eq] using hh

theorem principal_closed_formula (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (principalForm (fun i => x i)).PosDef) :
    12*(principalForm (fun i => x i)).det * moment (principalForm (fun i => x i)) =
      eval x momentC1 := by
  rw [principal_moment_identity _ (fun e => hx e) hQ]
  apply eval_congr_bounded momentC1 10 _ _ momentC1_support
  intro i hi
  simp only [extendWeight, dif_pos hi]

end D4.Principal
