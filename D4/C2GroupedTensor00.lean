import D4.C2TensorData00
import D4.C2GroupedTensorPart00_00
import D4.C2GroupedTensorPart01_00
import D4.C2GroupedTensorPart02_00
import D4.C2GroupedTensorPart03_00
import D4.C2GroupedTensorPart04_00
import D4.C2GroupedTensorPart05_00
import D4.C2GroupedTensorPart06_00
import D4.C2GroupedTensorPart07_00
import D4.C2GroupedTensorPart08_00
import D4.C2GroupedTensorPart09_00
import D4.C2GroupedTensorPart10_00
import D4.C2GroupedTensorPart11_00
import D4.C2GroupedTensorPart12_00
import D4.C2GroupedTensorPart13_00
import D4.C2GroupedTensorPart14_00
import D4.C2GroupedDeterminants
import D4.C2GroupedTensorPartition
import D4.CertificateBlocks228
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c2Tensor00_merge_check : sumFast [c2GroupedPart0_00,c2GroupedPart1_00,c2GroupedPart2_00,c2GroupedPart3_00,c2GroupedPart4_00,c2GroupedPart5_00,c2GroupedPart6_00,c2GroupedPart7_00,c2GroupedPart8_00,c2GroupedPart9_00,c2GroupedPart10_00,c2GroupedPart11_00,c2GroupedPart12_00,c2GroupedPart13_00,c2GroupedPart14_00] = c2Tensor00 := by kernel_rfl
theorem c2Tensor00_check :
    sumFast (c2TensorGroups.map (fun g => cellGroupedTensor c2VertexCoefficients c2Cell c2CellDetPoly g.1 g.2 0 0)) = c2Tensor00 := by
  simp only [c2TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_228]
  simpa (config := {implicitDefEqProofs := false}) only [
    c2GroupedPart0_00_raw_check,
    c2GroupedPart1_00_raw_check,
    c2GroupedPart2_00_raw_check,
    c2GroupedPart3_00_raw_check,
    c2GroupedPart4_00_raw_check,
    c2GroupedPart5_00_raw_check,
    c2GroupedPart6_00_raw_check,
    c2GroupedPart7_00_raw_check,
    c2GroupedPart8_00_raw_check,
    c2GroupedPart9_00_raw_check,
    c2GroupedPart10_00_raw_check,
    c2GroupedPart11_00_raw_check,
    c2GroupedPart12_00_raw_check,
    c2GroupedPart13_00_raw_check,
    c2GroupedPart14_00_raw_check] using c2Tensor00_merge_check

theorem c2Tensor00_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c2Tensor00 =
    ∑ t,eval (extendWeight w) (c2CellDetPoly t)*cellHessian (secondaryVertex c2VertexCoefficients w) (c2Cell t) 0 0 := by
  rw [← c2Tensor00_check]
  exact cellGroupedTensorFull_eval c2VertexCoefficients c2Cell c2CellDetPoly c2TensorGroups
    c2_group_determinants c2_tensor_groups_partition w 0 0
end
end D4.Secondary
