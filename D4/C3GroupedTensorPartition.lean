import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3_tensor_groups_sorted :
    CertificateSort.sort (fun (a b : Fin 582) => decide (a.val ≤ b.val))
      ((c3TensorGroups.map Prod.snd).flatten) = List.ofFn (fun t : Fin 582 => t) := by kernel_rfl

theorem c3_tensor_groups_partition :
    (c3TensorGroups.map Prod.snd).flatten.Perm (List.ofFn (fun t : Fin 582 => t)) := by
  have h := CertificateSort.sort_perm (fun (a b : Fin 582) => decide (a.val ≤ b.val))
    ((c3TensorGroups.map Prod.snd).flatten)
  rw [c3_tensor_groups_sorted] at h
  exact h.symm
end D4.Secondary
