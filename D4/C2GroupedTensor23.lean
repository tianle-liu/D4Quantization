import D4.C2TensorData23
import D4.C2GroupedTensorPart00_23
import D4.C2GroupedTensorPart01_23
import D4.C2GroupedTensorPart02_23
import D4.C2GroupedTensorPart03_23
import D4.C2GroupedTensorPart04_23
import D4.C2GroupedTensorPart05_23
import D4.C2GroupedTensorPart06_23
import D4.C2GroupedTensorPart07_23
import D4.C2GroupedTensorPart08_23
import D4.C2GroupedTensorPart09_23
import D4.C2GroupedTensorPart10_23
import D4.C2GroupedTensorPart11_23
import D4.C2GroupedTensorPart12_23
import D4.C2GroupedTensorPart13_23
import D4.C2GroupedTensorPart14_23
import D4.C2GroupedDeterminants
import D4.C2GroupedTensorPartition
import D4.CertificateBlocks228
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c2Tensor23_merge_check : sumFast [c2GroupedPart0_23,c2GroupedPart1_23,c2GroupedPart2_23,c2GroupedPart3_23,c2GroupedPart4_23,c2GroupedPart5_23,c2GroupedPart6_23,c2GroupedPart7_23,c2GroupedPart8_23,c2GroupedPart9_23,c2GroupedPart10_23,c2GroupedPart11_23,c2GroupedPart12_23,c2GroupedPart13_23,c2GroupedPart14_23] = c2Tensor23 := by kernel_rfl
theorem c2Tensor23_check :
    sumFast (c2TensorGroups.map (fun g => cellGroupedTensor c2VertexCoefficients c2Cell c2CellDetPoly g.1 g.2 2 3)) = c2Tensor23 := by
  simp only [c2TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_228]
  simpa (config := {implicitDefEqProofs := false}) only [
    c2GroupedPart0_23_raw_check,
    c2GroupedPart1_23_raw_check,
    c2GroupedPart2_23_raw_check,
    c2GroupedPart3_23_raw_check,
    c2GroupedPart4_23_raw_check,
    c2GroupedPart5_23_raw_check,
    c2GroupedPart6_23_raw_check,
    c2GroupedPart7_23_raw_check,
    c2GroupedPart8_23_raw_check,
    c2GroupedPart9_23_raw_check,
    c2GroupedPart10_23_raw_check,
    c2GroupedPart11_23_raw_check,
    c2GroupedPart12_23_raw_check,
    c2GroupedPart13_23_raw_check,
    c2GroupedPart14_23_raw_check] using c2Tensor23_merge_check

theorem c2Tensor23_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c2Tensor23 =
    ∑ t,eval (extendWeight w) (c2CellDetPoly t)*cellHessian (secondaryVertex c2VertexCoefficients w) (c2Cell t) 2 3 := by
  rw [← c2Tensor23_check]
  exact cellGroupedTensorFull_eval c2VertexCoefficients c2Cell c2CellDetPoly c2TensorGroups
    c2_group_determinants c2_tensor_groups_partition w 2 3
end
end D4.Secondary
