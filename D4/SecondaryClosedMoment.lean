import D4.C2MomentIdentity
import D4.C3MomentIdentity
import D4.PrincipalClosedMoment

noncomputable section
namespace D4.Secondary
open Matrix Analytic Principal Certificate CertificateMoments

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem momentC2_support : ∀ t ∈ momentC2, ∀ i ∈ t.1, i < 10 := by
  have hh : momentC2.all (fun t => t.1.all (fun i => decide (i < 10))) = true := by kernel_rfl
  intro t ht i hi
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hh t ht) i hi)

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem momentC3_support : ∀ t ∈ momentC3, ∀ i ∈ t.1, i < 10 := by
  have hh : momentC3.all (fun t => t.1.all (fun i => decide (i < 10))) = true := by kernel_rfl
  intro t ht i hi
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hh t ht) i hi)

theorem secondary2_closed_formula (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).PosDef) :
    60*(secondaryForm cone2Vectors (x 0) (fun i => x (i+1))).det *
      moment (secondaryForm cone2Vectors (x 0) (fun i => x (i+1))) = eval x momentC2 := by
  have h := c2_moment_identity (fun i => x i.val) (fun i => hx i.val) hQ
  refine h.trans ?_
  apply eval_congr_bounded momentC2 10 _ _ momentC2_support
  intro i hi
  simp only [extendWeight,dif_pos hi]

theorem secondary3_closed_formula (x : Nat → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hQ : (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).PosDef) :
    60*(secondaryForm cone3Vectors (x 0) (fun i => x (i+1))).det *
      moment (secondaryForm cone3Vectors (x 0) (fun i => x (i+1))) = eval x momentC3 := by
  have h := c3_moment_identity (fun i => x i.val) (fun i => hx i.val) hQ
  refine h.trans ?_
  apply eval_congr_bounded momentC3 10 _ _ momentC3_support
  intro i hi
  simp only [extendWeight,dif_pos hi]

end D4.Secondary
