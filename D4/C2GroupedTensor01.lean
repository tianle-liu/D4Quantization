import D4.C2TensorData01
import D4.C2GroupedTensorPart00_01
import D4.C2GroupedTensorPart01_01
import D4.C2GroupedTensorPart02_01
import D4.C2GroupedTensorPart03_01
import D4.C2GroupedTensorPart04_01
import D4.C2GroupedTensorPart05_01
import D4.C2GroupedTensorPart06_01
import D4.C2GroupedTensorPart07_01
import D4.C2GroupedTensorPart08_01
import D4.C2GroupedTensorPart09_01
import D4.C2GroupedTensorPart10_01
import D4.C2GroupedTensorPart11_01
import D4.C2GroupedTensorPart12_01
import D4.C2GroupedTensorPart13_01
import D4.C2GroupedTensorPart14_01
import D4.C2GroupedDeterminants
import D4.C2GroupedTensorPartition
import D4.CertificateBlocks228
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c2Tensor01_merge_check : sumFast [c2GroupedPart0_01,c2GroupedPart1_01,c2GroupedPart2_01,c2GroupedPart3_01,c2GroupedPart4_01,c2GroupedPart5_01,c2GroupedPart6_01,c2GroupedPart7_01,c2GroupedPart8_01,c2GroupedPart9_01,c2GroupedPart10_01,c2GroupedPart11_01,c2GroupedPart12_01,c2GroupedPart13_01,c2GroupedPart14_01] = c2Tensor01 := by kernel_rfl
theorem c2Tensor01_check :
    sumFast (c2TensorGroups.map (fun g => cellGroupedTensor c2VertexCoefficients c2Cell c2CellDetPoly g.1 g.2 0 1)) = c2Tensor01 := by
  simp only [c2TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_228]
  simpa (config := {implicitDefEqProofs := false}) only [
    c2GroupedPart0_01_raw_check,
    c2GroupedPart1_01_raw_check,
    c2GroupedPart2_01_raw_check,
    c2GroupedPart3_01_raw_check,
    c2GroupedPart4_01_raw_check,
    c2GroupedPart5_01_raw_check,
    c2GroupedPart6_01_raw_check,
    c2GroupedPart7_01_raw_check,
    c2GroupedPart8_01_raw_check,
    c2GroupedPart9_01_raw_check,
    c2GroupedPart10_01_raw_check,
    c2GroupedPart11_01_raw_check,
    c2GroupedPart12_01_raw_check,
    c2GroupedPart13_01_raw_check,
    c2GroupedPart14_01_raw_check] using c2Tensor01_merge_check

theorem c2Tensor01_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c2Tensor01 =
    ∑ t,eval (extendWeight w) (c2CellDetPoly t)*cellHessian (secondaryVertex c2VertexCoefficients w) (c2Cell t) 0 1 := by
  rw [← c2Tensor01_check]
  exact cellGroupedTensorFull_eval c2VertexCoefficients c2Cell c2CellDetPoly c2TensorGroups
    c2_group_determinants c2_tensor_groups_partition w 0 1
end
end D4.Secondary
