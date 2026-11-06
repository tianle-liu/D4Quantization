import D4.C2TensorData13
import D4.C2GroupedTensorPart00_13
import D4.C2GroupedTensorPart01_13
import D4.C2GroupedTensorPart02_13
import D4.C2GroupedTensorPart03_13
import D4.C2GroupedTensorPart04_13
import D4.C2GroupedTensorPart05_13
import D4.C2GroupedTensorPart06_13
import D4.C2GroupedTensorPart07_13
import D4.C2GroupedTensorPart08_13
import D4.C2GroupedTensorPart09_13
import D4.C2GroupedTensorPart10_13
import D4.C2GroupedTensorPart11_13
import D4.C2GroupedTensorPart12_13
import D4.C2GroupedTensorPart13_13
import D4.C2GroupedTensorPart14_13
import D4.C2GroupedDeterminants
import D4.C2GroupedTensorPartition
import D4.CertificateBlocks228
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c2Tensor13_merge_check : sumFast [c2GroupedPart0_13,c2GroupedPart1_13,c2GroupedPart2_13,c2GroupedPart3_13,c2GroupedPart4_13,c2GroupedPart5_13,c2GroupedPart6_13,c2GroupedPart7_13,c2GroupedPart8_13,c2GroupedPart9_13,c2GroupedPart10_13,c2GroupedPart11_13,c2GroupedPart12_13,c2GroupedPart13_13,c2GroupedPart14_13] = c2Tensor13 := by kernel_rfl
theorem c2Tensor13_check :
    sumFast (c2TensorGroups.map (fun g => cellGroupedTensor c2VertexCoefficients c2Cell c2CellDetPoly g.1 g.2 1 3)) = c2Tensor13 := by
  simp only [c2TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_228]
  simpa (config := {implicitDefEqProofs := false}) only [
    c2GroupedPart0_13_raw_check,
    c2GroupedPart1_13_raw_check,
    c2GroupedPart2_13_raw_check,
    c2GroupedPart3_13_raw_check,
    c2GroupedPart4_13_raw_check,
    c2GroupedPart5_13_raw_check,
    c2GroupedPart6_13_raw_check,
    c2GroupedPart7_13_raw_check,
    c2GroupedPart8_13_raw_check,
    c2GroupedPart9_13_raw_check,
    c2GroupedPart10_13_raw_check,
    c2GroupedPart11_13_raw_check,
    c2GroupedPart12_13_raw_check,
    c2GroupedPart13_13_raw_check,
    c2GroupedPart14_13_raw_check] using c2Tensor13_merge_check

theorem c2Tensor13_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c2Tensor13 =
    ∑ t,eval (extendWeight w) (c2CellDetPoly t)*cellHessian (secondaryVertex c2VertexCoefficients w) (c2Cell t) 1 3 := by
  rw [← c2Tensor13_check]
  exact cellGroupedTensorFull_eval c2VertexCoefficients c2Cell c2CellDetPoly c2TensorGroups
    c2_group_determinants c2_tensor_groups_partition w 1 3
end
end D4.Secondary
