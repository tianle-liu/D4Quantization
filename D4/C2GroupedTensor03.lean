import D4.C2TensorData03
import D4.C2GroupedTensorPart00_03
import D4.C2GroupedTensorPart01_03
import D4.C2GroupedTensorPart02_03
import D4.C2GroupedTensorPart03_03
import D4.C2GroupedTensorPart04_03
import D4.C2GroupedTensorPart05_03
import D4.C2GroupedTensorPart06_03
import D4.C2GroupedTensorPart07_03
import D4.C2GroupedTensorPart08_03
import D4.C2GroupedTensorPart09_03
import D4.C2GroupedTensorPart10_03
import D4.C2GroupedTensorPart11_03
import D4.C2GroupedTensorPart12_03
import D4.C2GroupedTensorPart13_03
import D4.C2GroupedTensorPart14_03
import D4.C2GroupedDeterminants
import D4.C2GroupedTensorPartition
import D4.CertificateBlocks228
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c2Tensor03_merge_check : sumFast [c2GroupedPart0_03,c2GroupedPart1_03,c2GroupedPart2_03,c2GroupedPart3_03,c2GroupedPart4_03,c2GroupedPart5_03,c2GroupedPart6_03,c2GroupedPart7_03,c2GroupedPart8_03,c2GroupedPart9_03,c2GroupedPart10_03,c2GroupedPart11_03,c2GroupedPart12_03,c2GroupedPart13_03,c2GroupedPart14_03] = c2Tensor03 := by kernel_rfl
theorem c2Tensor03_check :
    sumFast (c2TensorGroups.map (fun g => cellGroupedTensor c2VertexCoefficients c2Cell c2CellDetPoly g.1 g.2 0 3)) = c2Tensor03 := by
  simp only [c2TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_228]
  simpa (config := {implicitDefEqProofs := false}) only [
    c2GroupedPart0_03_raw_check,
    c2GroupedPart1_03_raw_check,
    c2GroupedPart2_03_raw_check,
    c2GroupedPart3_03_raw_check,
    c2GroupedPart4_03_raw_check,
    c2GroupedPart5_03_raw_check,
    c2GroupedPart6_03_raw_check,
    c2GroupedPart7_03_raw_check,
    c2GroupedPart8_03_raw_check,
    c2GroupedPart9_03_raw_check,
    c2GroupedPart10_03_raw_check,
    c2GroupedPart11_03_raw_check,
    c2GroupedPart12_03_raw_check,
    c2GroupedPart13_03_raw_check,
    c2GroupedPart14_03_raw_check] using c2Tensor03_merge_check

theorem c2Tensor03_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c2Tensor03 =
    ∑ t,eval (extendWeight w) (c2CellDetPoly t)*cellHessian (secondaryVertex c2VertexCoefficients w) (c2Cell t) 0 3 := by
  rw [← c2Tensor03_check]
  exact cellGroupedTensorFull_eval c2VertexCoefficients c2Cell c2CellDetPoly c2TensorGroups
    c2_group_determinants c2_tensor_groups_partition w 0 3
end
end D4.Secondary
