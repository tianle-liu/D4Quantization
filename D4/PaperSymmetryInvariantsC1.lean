import D4.PaperSymmetryC1Generation
import D4.CertificateMomentData
import D4.KernelCompute
set_option maxRecDepth 1000000
namespace D4.PaperSymmetry.C1
open D4.Certificate D4.CertificateMoments

theorem determinant_support_check : determinantC1.all (fun t => t.1.all (fun i => decide (i<10)))=true := by kernel_rfl
theorem determinant_support : ∀ t ∈ determinantC1, ∀ i ∈ t.1, i<10 := by
  simpa only [List.all_eq_true,decide_eq_true_eq] using determinant_support_check
theorem determinant_g0 : rename (encoding (edgeHom (Equiv.swap (0:Fin 5) (1:Fin 5)))) determinantC1=determinantC1 := by kernel_rfl
theorem determinant_g1 : rename (encoding (edgeHom (Equiv.swap (1:Fin 5) (2:Fin 5)))) determinantC1=determinantC1 := by kernel_rfl
theorem determinant_g2 : rename (encoding (edgeHom (Equiv.swap (2:Fin 5) (3:Fin 5)))) determinantC1=determinantC1 := by kernel_rfl
theorem determinant_g3 : rename (encoding (edgeHom (Equiv.swap (3:Fin 5) (4:Fin 5)))) determinantC1=determinantC1 := by kernel_rfl
theorem determinant_invariant (p : Equiv.Perm (Fin 5)) (x : Nat → ℝ) :
    eval (fun n => x (extend (edgeHom p) n)) determinantC1=eval x determinantC1 := by
  apply invariant_all (fun x => eval x determinantC1) ?_ p x
  intro i
  fin_cases i
  · exact invariant_of_rename determinantC1 _ determinant_support determinant_g0
  · exact invariant_of_rename determinantC1 _ determinant_support determinant_g1
  · exact invariant_of_rename determinantC1 _ determinant_support determinant_g2
  · exact invariant_of_rename determinantC1 _ determinant_support determinant_g3

theorem moment_support_check : momentC1.all (fun t => t.1.all (fun i => decide (i<10)))=true := by kernel_rfl
theorem moment_support : ∀ t ∈ momentC1, ∀ i ∈ t.1, i<10 := by
  simpa only [List.all_eq_true,decide_eq_true_eq] using moment_support_check
theorem moment_g0 : rename (encoding (edgeHom (Equiv.swap (0:Fin 5) (1:Fin 5)))) momentC1=momentC1 := by kernel_rfl
theorem moment_g1 : rename (encoding (edgeHom (Equiv.swap (1:Fin 5) (2:Fin 5)))) momentC1=momentC1 := by kernel_rfl
theorem moment_g2 : rename (encoding (edgeHom (Equiv.swap (2:Fin 5) (3:Fin 5)))) momentC1=momentC1 := by kernel_rfl
theorem moment_g3 : rename (encoding (edgeHom (Equiv.swap (3:Fin 5) (4:Fin 5)))) momentC1=momentC1 := by kernel_rfl
theorem moment_invariant (p : Equiv.Perm (Fin 5)) (x : Nat → ℝ) :
    eval (fun n => x (extend (edgeHom p) n)) momentC1=eval x momentC1 := by
  apply invariant_all (fun x => eval x momentC1) ?_ p x
  intro i
  fin_cases i
  · exact invariant_of_rename momentC1 _ moment_support moment_g0
  · exact invariant_of_rename momentC1 _ moment_support moment_g1
  · exact invariant_of_rename momentC1 _ moment_support moment_g2
  · exact invariant_of_rename momentC1 _ moment_support moment_g3

theorem parameter_support_check : parameterC1.all (fun t => t.1.all (fun i => decide (i<10)))=true := by kernel_rfl
theorem parameter_support : ∀ t ∈ parameterC1, ∀ i ∈ t.1, i<10 := by
  simpa only [List.all_eq_true,decide_eq_true_eq] using parameter_support_check
theorem parameter_g0 : rename (encoding (edgeHom (Equiv.swap (0:Fin 5) (1:Fin 5)))) parameterC1=parameterC1 := by kernel_rfl
theorem parameter_g1 : rename (encoding (edgeHom (Equiv.swap (1:Fin 5) (2:Fin 5)))) parameterC1=parameterC1 := by kernel_rfl
theorem parameter_g2 : rename (encoding (edgeHom (Equiv.swap (2:Fin 5) (3:Fin 5)))) parameterC1=parameterC1 := by kernel_rfl
theorem parameter_g3 : rename (encoding (edgeHom (Equiv.swap (3:Fin 5) (4:Fin 5)))) parameterC1=parameterC1 := by kernel_rfl
theorem parameter_invariant (p : Equiv.Perm (Fin 5)) (x : Nat → ℝ) :
    eval (fun n => x (extend (edgeHom p) n)) parameterC1=eval x parameterC1 := by
  apply invariant_all (fun x => eval x parameterC1) ?_ p x
  intro i
  fin_cases i
  · exact invariant_of_rename parameterC1 _ parameter_support parameter_g0
  · exact invariant_of_rename parameterC1 _ parameter_support parameter_g1
  · exact invariant_of_rename parameterC1 _ parameter_support parameter_g2
  · exact invariant_of_rename parameterC1 _ parameter_support parameter_g3

end D4.PaperSymmetry.C1
