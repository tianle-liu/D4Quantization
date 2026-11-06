import D4.C2TensorData11
import D4.C2GroupedTensorPart00_11
import D4.C2GroupedTensorPart01_11
import D4.C2GroupedTensorPart02_11
import D4.C2GroupedTensorPart03_11
import D4.C2GroupedTensorPart04_11
import D4.C2GroupedTensorPart05_11
import D4.C2GroupedTensorPart06_11
import D4.C2GroupedTensorPart07_11
import D4.C2GroupedTensorPart08_11
import D4.C2GroupedTensorPart09_11
import D4.C2GroupedTensorPart10_11
import D4.C2GroupedTensorPart11_11
import D4.C2GroupedTensorPart12_11
import D4.C2GroupedTensorPart13_11
import D4.C2GroupedTensorPart14_11
import D4.C2GroupedDeterminants
import D4.C2GroupedTensorPartition
import D4.CertificateBlocks228
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c2Tensor11_merge_check : sumFast [c2GroupedPart0_11,c2GroupedPart1_11,c2GroupedPart2_11,c2GroupedPart3_11,c2GroupedPart4_11,c2GroupedPart5_11,c2GroupedPart6_11,c2GroupedPart7_11,c2GroupedPart8_11,c2GroupedPart9_11,c2GroupedPart10_11,c2GroupedPart11_11,c2GroupedPart12_11,c2GroupedPart13_11,c2GroupedPart14_11] = c2Tensor11 := by kernel_rfl
theorem c2Tensor11_check :
    sumFast (c2TensorGroups.map (fun g => cellGroupedTensor c2VertexCoefficients c2Cell c2CellDetPoly g.1 g.2 1 1)) = c2Tensor11 := by
  simp only [c2TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_228]
  simpa (config := {implicitDefEqProofs := false}) only [
    c2GroupedPart0_11_raw_check,
    c2GroupedPart1_11_raw_check,
    c2GroupedPart2_11_raw_check,
    c2GroupedPart3_11_raw_check,
    c2GroupedPart4_11_raw_check,
    c2GroupedPart5_11_raw_check,
    c2GroupedPart6_11_raw_check,
    c2GroupedPart7_11_raw_check,
    c2GroupedPart8_11_raw_check,
    c2GroupedPart9_11_raw_check,
    c2GroupedPart10_11_raw_check,
    c2GroupedPart11_11_raw_check,
    c2GroupedPart12_11_raw_check,
    c2GroupedPart13_11_raw_check,
    c2GroupedPart14_11_raw_check] using c2Tensor11_merge_check

theorem c2Tensor11_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c2Tensor11 =
    ∑ t,eval (extendWeight w) (c2CellDetPoly t)*cellHessian (secondaryVertex c2VertexCoefficients w) (c2Cell t) 1 1 := by
  rw [← c2Tensor11_check]
  exact cellGroupedTensorFull_eval c2VertexCoefficients c2Cell c2CellDetPoly c2TensorGroups
    c2_group_determinants c2_tensor_groups_partition w 1 1
end
end D4.Secondary
