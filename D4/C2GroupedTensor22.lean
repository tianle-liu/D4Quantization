import D4.C2TensorData22
import D4.C2GroupedTensorPart00_22
import D4.C2GroupedTensorPart01_22
import D4.C2GroupedTensorPart02_22
import D4.C2GroupedTensorPart03_22
import D4.C2GroupedTensorPart04_22
import D4.C2GroupedTensorPart05_22
import D4.C2GroupedTensorPart06_22
import D4.C2GroupedTensorPart07_22
import D4.C2GroupedTensorPart08_22
import D4.C2GroupedTensorPart09_22
import D4.C2GroupedTensorPart10_22
import D4.C2GroupedTensorPart11_22
import D4.C2GroupedTensorPart12_22
import D4.C2GroupedTensorPart13_22
import D4.C2GroupedTensorPart14_22
import D4.C2GroupedDeterminants
import D4.C2GroupedTensorPartition
import D4.CertificateBlocks228
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c2Tensor22_merge_check : sumFast [c2GroupedPart0_22,c2GroupedPart1_22,c2GroupedPart2_22,c2GroupedPart3_22,c2GroupedPart4_22,c2GroupedPart5_22,c2GroupedPart6_22,c2GroupedPart7_22,c2GroupedPart8_22,c2GroupedPart9_22,c2GroupedPart10_22,c2GroupedPart11_22,c2GroupedPart12_22,c2GroupedPart13_22,c2GroupedPart14_22] = c2Tensor22 := by kernel_rfl
theorem c2Tensor22_check :
    sumFast (c2TensorGroups.map (fun g => cellGroupedTensor c2VertexCoefficients c2Cell c2CellDetPoly g.1 g.2 2 2)) = c2Tensor22 := by
  simp only [c2TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_228]
  simpa (config := {implicitDefEqProofs := false}) only [
    c2GroupedPart0_22_raw_check,
    c2GroupedPart1_22_raw_check,
    c2GroupedPart2_22_raw_check,
    c2GroupedPart3_22_raw_check,
    c2GroupedPart4_22_raw_check,
    c2GroupedPart5_22_raw_check,
    c2GroupedPart6_22_raw_check,
    c2GroupedPart7_22_raw_check,
    c2GroupedPart8_22_raw_check,
    c2GroupedPart9_22_raw_check,
    c2GroupedPart10_22_raw_check,
    c2GroupedPart11_22_raw_check,
    c2GroupedPart12_22_raw_check,
    c2GroupedPart13_22_raw_check,
    c2GroupedPart14_22_raw_check] using c2Tensor22_merge_check

theorem c2Tensor22_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c2Tensor22 =
    ∑ t,eval (extendWeight w) (c2CellDetPoly t)*cellHessian (secondaryVertex c2VertexCoefficients w) (c2Cell t) 2 2 := by
  rw [← c2Tensor22_check]
  exact cellGroupedTensorFull_eval c2VertexCoefficients c2Cell c2CellDetPoly c2TensorGroups
    c2_group_determinants c2_tensor_groups_partition w 2 2
end
end D4.Secondary
