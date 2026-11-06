import D4.PrincipalGraphList
import D4.PrincipalGraphCounts
import D4.CertificateMomentC1Checks
import D4.CertificateFast

namespace D4.PrincipalGraphs
open Certificate CertificateMoments
open scoped BigOperators

def edgeList (H : Finset (Fin 10)) : List (Fin 10) :=
  (List.finRange 10).filter fun e => decide (e ∈ H)

theorem edgeList_nodup (H : Finset (Fin 10)) : (edgeList H).Nodup :=
  (List.nodup_finRange 10).filter _

theorem edgeList_toFinset (H : Finset (Fin 10)) : (edgeList H).toFinset = H := by
  ext e
  simp [edgeList, List.mem_finRange]

def graphCyclePolynomial : Poly := sumFast <|
  (fiveEdgeList.filter fun H => decide (NoIsolated H)).map fun H =>
    [((edgeList H).map Fin.val, (cycleCore H).card-2)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem graphCyclePolynomial_check : graphCyclePolynomial = baseC1 := by kernel_rfl

noncomputable def graphCycleSum (x : Nat → ℝ) : ℝ :=
  ∑ H ∈ fiveEdgeGraphs.filter (fun H => (graph H).Connected),
    ((cycleCore H).card-2:ℝ) * ∏ e ∈ H, x e.val

theorem monomial_graph (x : Nat → ℝ) (H : Finset (Fin 10)) :
    monomial x ((edgeList H).map Fin.val) = ∏ e ∈ H, x e.val := by
  simp only [monomial,List.map_map,Function.comp_def]
  rw [← List.prod_toFinset _ (edgeList_nodup H),edgeList_toFinset]

theorem graphCyclePolynomial_eval (x : Nat → ℝ) :
    eval x graphCyclePolynomial = graphCycleSum x := by
  rw [graphCyclePolynomial,eval_sumFast]
  simp only [List.map_map, Function.comp_def, eval_cons, eval_nil, add_zero,
    Int.cast_sub, Int.cast_natCast, Int.cast_ofNat,monomial_graph]
  rw [← List.sum_toFinset _ (fiveEdgeList_nodup.filter _)]
  rw [List.toFinset_filter,fiveEdgeList_toFinset]
  have hfilter : fiveEdgeGraphs.filter (fun H => decide (NoIsolated H)) =
      fiveEdgeGraphs.filter (fun H => (graph H).Connected) := by
    apply Finset.filter_congr
    intro H hH
    have hc : H.card=5 := by simpa [fiveEdgeGraphs] using hH
    simp only [decide_eq_true_eq,connected_iff_noIsolated hc]
  rw [hfilter]
  rfl

theorem momentC1_graph_formula (x : Nat → ℝ) :
    eval x momentC1 = eval x determinantC1 * eval x parameterC1 + graphCycleSum x := by
  have h := congrArg (eval x) base_identity_C1
  rw [eval_mergeAdd,eval_scale, ← determinant_product_C1,eval_mul,
    ← graphCyclePolynomial_check,graphCyclePolynomial_eval] at h
  norm_num at h
  linarith

end D4.PrincipalGraphs
