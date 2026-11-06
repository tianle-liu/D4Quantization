import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2_tensor_groups_sorted :
    CertificateSort.sort (fun (a b : Fin 580) => decide (a.val ≤ b.val))
      ((c2TensorGroups.map Prod.snd).flatten) = List.ofFn (fun t : Fin 580 => t) := by kernel_rfl

theorem c2_tensor_groups_partition :
    (c2TensorGroups.map Prod.snd).flatten.Perm (List.ofFn (fun t : Fin 580 => t)) := by
  have h := CertificateSort.sort_perm (fun (a b : Fin 580) => decide (a.val ≤ b.val))
    ((c2TensorGroups.map Prod.snd).flatten)
  rw [c2_tensor_groups_sorted] at h
  exact h.symm
end D4.Secondary
