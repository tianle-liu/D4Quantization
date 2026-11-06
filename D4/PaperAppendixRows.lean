import D4.CertificateC1B1Data
import D4.CertificateC1B2Data
import D4.CertificateC2B1Data
import D4.CertificateC2B2Data
import D4.CertificateC3B1Data
import D4.CertificateC3B2Data
import D4.KernelCompute

namespace D4.PaperAppendix
open Certificate

def positiveWeights (rows : List Row) : Bool :=
  rows.all fun r => !r.weight.isEmpty && r.weight.all (fun t => decide (0<t.2))

theorem positiveWeights_sound (rows : List Row) (h : positiveWeights rows=true) :
    ∀ r∈rows,r.weight≠[] ∧ ∀ t∈r.weight,0<t.2 := by
  intro r hr
  have hh := List.all_eq_true.mp h r hr
  simp only [Bool.and_eq_true] at hh
  refine ⟨?_,fun t ht => of_decide_eq_true (List.all_eq_true.mp hh.2 t ht)⟩
  intro hz
  simpa only [hz,List.isEmpty_nil,Bool.not_true,Bool.false_eq_true] using hh.1

theorem c1b1_row_count : CertificateC1B1.rows.length=7 := by kernel_rfl

theorem c1b1_positiveWeights : positiveWeights CertificateC1B1.rows=true := by kernel_rfl

theorem c1b1_weights_positive : ∀ r∈CertificateC1B1.rows,
    r.weight≠[] ∧ ∀ t∈r.weight,0<t.2 :=
  positiveWeights_sound _ c1b1_positiveWeights

theorem c1b2_row_count : CertificateC1B2.rows.length=6 := by kernel_rfl

theorem c1b2_positiveWeights : positiveWeights CertificateC1B2.rows=true := by kernel_rfl

theorem c1b2_weights_positive : ∀ r∈CertificateC1B2.rows,
    r.weight≠[] ∧ ∀ t∈r.weight,0<t.2 :=
  positiveWeights_sound _ c1b2_positiveWeights

theorem c2b1_row_count : CertificateC2B1.rows.length=20 := by kernel_rfl

theorem c2b1_positiveWeights : positiveWeights CertificateC2B1.rows=true := by kernel_rfl

theorem c2b1_weights_positive : ∀ r∈CertificateC2B1.rows,
    r.weight≠[] ∧ ∀ t∈r.weight,0<t.2 :=
  positiveWeights_sound _ c2b1_positiveWeights

theorem c2b2_row_count : CertificateC2B2.rows.length=17 := by kernel_rfl

theorem c2b2_positiveWeights : positiveWeights CertificateC2B2.rows=true := by kernel_rfl

theorem c2b2_weights_positive : ∀ r∈CertificateC2B2.rows,
    r.weight≠[] ∧ ∀ t∈r.weight,0<t.2 :=
  positiveWeights_sound _ c2b2_positiveWeights

theorem c3b1_row_count : CertificateC3B1.rows.length=12 := by kernel_rfl

theorem c3b1_positiveWeights : positiveWeights CertificateC3B1.rows=true := by kernel_rfl

theorem c3b1_weights_positive : ∀ r∈CertificateC3B1.rows,
    r.weight≠[] ∧ ∀ t∈r.weight,0<t.2 :=
  positiveWeights_sound _ c3b1_positiveWeights

theorem c3b2_row_count : CertificateC3B2.rows.length=10 := by kernel_rfl

theorem c3b2_positiveWeights : positiveWeights CertificateC3B2.rows=true := by kernel_rfl

theorem c3b2_weights_positive : ∀ r∈CertificateC3B2.rows,
    r.weight≠[] ∧ ∀ t∈r.weight,0<t.2 :=
  positiveWeights_sound _ c3b2_positiveWeights

end D4.PaperAppendix
