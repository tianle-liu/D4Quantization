import D4.C2TensorData12
import D4.C2GroupedTensorPart00_12
import D4.C2GroupedTensorPart01_12
import D4.C2GroupedTensorPart02_12
import D4.C2GroupedTensorPart03_12
import D4.C2GroupedTensorPart04_12
import D4.C2GroupedTensorPart05_12
import D4.C2GroupedTensorPart06_12
import D4.C2GroupedTensorPart07_12
import D4.C2GroupedTensorPart08_12
import D4.C2GroupedTensorPart09_12
import D4.C2GroupedTensorPart10_12
import D4.C2GroupedTensorPart11_12
import D4.C2GroupedTensorPart12_12
import D4.C2GroupedTensorPart13_12
import D4.C2GroupedTensorPart14_12
import D4.C2GroupedDeterminants
import D4.C2GroupedTensorPartition
import D4.CertificateBlocks228
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c2Tensor12_merge_check : sumFast [c2GroupedPart0_12,c2GroupedPart1_12,c2GroupedPart2_12,c2GroupedPart3_12,c2GroupedPart4_12,c2GroupedPart5_12,c2GroupedPart6_12,c2GroupedPart7_12,c2GroupedPart8_12,c2GroupedPart9_12,c2GroupedPart10_12,c2GroupedPart11_12,c2GroupedPart12_12,c2GroupedPart13_12,c2GroupedPart14_12] = c2Tensor12 := by kernel_rfl
theorem c2Tensor12_check :
    sumFast (c2TensorGroups.map (fun g => cellGroupedTensor c2VertexCoefficients c2Cell c2CellDetPoly g.1 g.2 1 2)) = c2Tensor12 := by
  simp only [c2TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_228]
  simpa (config := {implicitDefEqProofs := false}) only [
    c2GroupedPart0_12_raw_check,
    c2GroupedPart1_12_raw_check,
    c2GroupedPart2_12_raw_check,
    c2GroupedPart3_12_raw_check,
    c2GroupedPart4_12_raw_check,
    c2GroupedPart5_12_raw_check,
    c2GroupedPart6_12_raw_check,
    c2GroupedPart7_12_raw_check,
    c2GroupedPart8_12_raw_check,
    c2GroupedPart9_12_raw_check,
    c2GroupedPart10_12_raw_check,
    c2GroupedPart11_12_raw_check,
    c2GroupedPart12_12_raw_check,
    c2GroupedPart13_12_raw_check,
    c2GroupedPart14_12_raw_check] using c2Tensor12_merge_check

theorem c2Tensor12_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c2Tensor12 =
    ∑ t,eval (extendWeight w) (c2CellDetPoly t)*cellHessian (secondaryVertex c2VertexCoefficients w) (c2Cell t) 1 2 := by
  rw [← c2Tensor12_check]
  exact cellGroupedTensorFull_eval c2VertexCoefficients c2Cell c2CellDetPoly c2TensorGroups
    c2_group_determinants c2_tensor_groups_partition w 1 2
end
end D4.Secondary
