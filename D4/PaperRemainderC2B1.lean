import D4.PaperCoefficientStatistics
import D4.CertificateC2B1Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.PaperStatistics.PaperRemainderC2B1
open D4.Certificate D4.PaperStatistics
abbrev p : Poly := D4.CertificateC2B1.remainder

theorem keys_check : decide ((p.map (fun t => key t.1)).Chain' (· < ·)) = true := by kernel_rfl

theorem degree_check : p.all (fun t => decide
    (t.1.length=5 ∧ t.1.Pairwise (· ≤ ·) ∧ ∀ i ∈ t.1, i<10)) = true := by kernel_rfl

theorem minimum_check : p.all (fun t => decide (76800 ≤ t.2)) = true := by kernel_rfl

theorem attained_check : p.any (fun t => decide (t.2=76800)) = true := by kernel_rfl

theorem length_check : p.length=2002 := by kernel_rfl

theorem nodup : (p.map Prod.fst).Nodup := keys_nodup p (of_decide_eq_true keys_check)

theorem degrees (t) (ht : t ∈ p) :
    t.1.length=5 ∧ t.1.Pairwise (· ≤ ·) ∧ ∀ i ∈ t.1, i<10 :=
  of_decide_eq_true (List.all_eq_true.mp degree_check t ht)

theorem minimum_bound (t) (ht : t ∈ p) : 76800 ≤ t.2 :=
  of_decide_eq_true (List.all_eq_true.mp minimum_check t ht)

theorem counts :
    (degreeFive.toFinset.filter (fun m => coefficient p m=0)).card=0 ∧
    (degreeFive.toFinset.filter (fun m => 0 < coefficient p m)).card=2002 := by
  have h := support_counts p 2002 nodup length_check
    (fun t ht => lt_of_lt_of_le (by norm_num) (minimum_bound t ht)) degrees
  exact ⟨by simpa using h.2,h.1⟩

theorem minimum_integer :
    (∀ m ∈ degreeFive, 0 < coefficient p m → 76800 ≤ coefficient p m) ∧
      ∃ m ∈ degreeFive, coefficient p m=76800 := by
  apply positive_minimum p 76800 (by norm_num) nodup minimum_bound _ degrees
  obtain ⟨t,ht,he⟩ := List.any_eq_true.mp attained_check
  exact ⟨t,ht,of_decide_eq_true he⟩

/-- The positive coefficients of the original rational remainder, after
undoing the exact integral scale used by the checked certificate. -/
theorem minimum_original :
    (∀ m ∈ degreeFive, 0 < coefficient p m →
      (1/192000:ℚ) ≤ (coefficient p m : ℚ)/14745600000) ∧
    ∃ m ∈ degreeFive, (coefficient p m : ℚ)/14745600000=(1/192000:ℚ) := by
  constructor
  · intro m hm hp
    have h : (76800:ℚ) ≤ (coefficient p m:ℚ) := by exact_mod_cast minimum_integer.1 m hm hp
    linarith
  · obtain ⟨m,hm,he⟩ := minimum_integer.2
    exact ⟨m,hm,by rw [he]; norm_num⟩

end D4.PaperStatistics.PaperRemainderC2B1
