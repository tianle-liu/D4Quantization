import D4.PaperSymmetryAction
import D4.PaperSymmetryC3
import D4.CertificateMomentData
import D4.KernelCompute
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.PaperSymmetry.C3
open D4.Certificate D4.CertificateMoments

theorem determinant_support_check : determinantC3.all (fun t => t.1.all (fun i => decide (i<10)))=true := by kernel_rfl

theorem determinant_support : ∀ t ∈ determinantC3, ∀ i ∈ t.1, i<10 := by
  simpa only [List.all_eq_true,decide_eq_true_eq] using determinant_support_check

theorem determinant_g0 : rename (encoding g0) determinantC3=determinantC3 := by kernel_rfl

theorem determinant_g1 : rename (encoding g1) determinantC3=determinantC3 := by kernel_rfl

theorem determinant_invariant {g : Perm} (hg : g ∈ Subgroup.closure ({g0,g1}:Set Perm)) (x : Nat → ℝ) :
    eval (fun n => x (extend g n)) determinantC3=eval x determinantC3 := by
  exact invariant_generated (fun x => eval x determinantC3) g0 g1
    (invariant_of_rename determinantC3 g0 determinant_support determinant_g0)
    (invariant_of_rename determinantC3 g1 determinant_support determinant_g1) hg x

theorem moment_support_check : momentC3.all (fun t => t.1.all (fun i => decide (i<10)))=true := by kernel_rfl

theorem moment_support : ∀ t ∈ momentC3, ∀ i ∈ t.1, i<10 := by
  simpa only [List.all_eq_true,decide_eq_true_eq] using moment_support_check

theorem moment_g0 : rename (encoding g0) momentC3=momentC3 := by kernel_rfl

theorem moment_g1 : rename (encoding g1) momentC3=momentC3 := by kernel_rfl

theorem moment_invariant {g : Perm} (hg : g ∈ Subgroup.closure ({g0,g1}:Set Perm)) (x : Nat → ℝ) :
    eval (fun n => x (extend g n)) momentC3=eval x momentC3 := by
  exact invariant_generated (fun x => eval x momentC3) g0 g1
    (invariant_of_rename momentC3 g0 moment_support moment_g0)
    (invariant_of_rename momentC3 g1 moment_support moment_g1) hg x

theorem parameter_support_check : parameterC3.all (fun t => t.1.all (fun i => decide (i<10)))=true := by kernel_rfl

theorem parameter_support : ∀ t ∈ parameterC3, ∀ i ∈ t.1, i<10 := by
  simpa only [List.all_eq_true,decide_eq_true_eq] using parameter_support_check

theorem parameter_g0 : rename (encoding g0) parameterC3=parameterC3 := by kernel_rfl

theorem parameter_g1 : rename (encoding g1) parameterC3=parameterC3 := by kernel_rfl

theorem parameter_invariant {g : Perm} (hg : g ∈ Subgroup.closure ({g0,g1}:Set Perm)) (x : Nat → ℝ) :
    eval (fun n => x (extend g n)) parameterC3=eval x parameterC3 := by
  exact invariant_generated (fun x => eval x parameterC3) g0 g1
    (invariant_of_rename parameterC3 g0 parameter_support parameter_g0)
    (invariant_of_rename parameterC3 g1 parameter_support parameter_g1) hg x

end D4.PaperSymmetry.C3
