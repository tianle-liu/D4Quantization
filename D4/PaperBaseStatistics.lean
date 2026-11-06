import D4.PaperCoefficientStatistics
import D4.CertificateMomentData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.PaperStatistics
open Certificate CertificateMoments

theorem base2_keys : decide ((baseC2.map (fun t => key t.1)).Chain' (· < ·))=true := by kernel_rfl
theorem base2_degree : baseC2.all (fun t => decide (t.1.length=5 ∧ t.1.Pairwise (· ≤ ·) ∧ ∀ i ∈ t.1, i<10))=true := by kernel_rfl
theorem base2_positive : baseC2.all (fun t => decide (0<t.2))=true := by kernel_rfl
theorem base2_length : baseC2.length=367 := by kernel_rfl
/-- The exact number of nonzero coefficients in the source's base difference. -/
theorem base2_counts :
    (degreeFive.toFinset.filter (fun m => 0 < coefficient baseC2 m)).card=367 ∧
    (degreeFive.toFinset.filter (fun m => coefficient baseC2 m=0)).card=1635 := by
  apply support_counts baseC2 367 (keys_nodup _ (of_decide_eq_true base2_keys)) base2_length
  · exact fun t ht => of_decide_eq_true (List.all_eq_true.mp base2_positive t ht)
  · exact fun t ht => of_decide_eq_true (List.all_eq_true.mp base2_degree t ht)

theorem base3_keys : decide ((baseC3.map (fun t => key t.1)).Chain' (· < ·))=true := by kernel_rfl
theorem base3_degree : baseC3.all (fun t => decide (t.1.length=5 ∧ t.1.Pairwise (· ≤ ·) ∧ ∀ i ∈ t.1, i<10))=true := by kernel_rfl
theorem base3_positive : baseC3.all (fun t => decide (0<t.2))=true := by kernel_rfl
theorem base3_length : baseC3.length=373 := by kernel_rfl
/-- The exact number of nonzero coefficients in the source's base difference. -/
theorem base3_counts :
    (degreeFive.toFinset.filter (fun m => 0 < coefficient baseC3 m)).card=373 ∧
    (degreeFive.toFinset.filter (fun m => coefficient baseC3 m=0)).card=1629 := by
  apply support_counts baseC3 373 (keys_nodup _ (of_decide_eq_true base3_keys)) base3_length
  · exact fun t ht => of_decide_eq_true (List.all_eq_true.mp base3_positive t ht)
  · exact fun t ht => of_decide_eq_true (List.all_eq_true.mp base3_degree t ht)
end D4.PaperStatistics
