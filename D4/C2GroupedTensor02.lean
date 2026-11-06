import D4.C2TensorData02
import D4.C2GroupedTensorPart00_02
import D4.C2GroupedTensorPart01_02
import D4.C2GroupedTensorPart02_02
import D4.C2GroupedTensorPart03_02
import D4.C2GroupedTensorPart04_02
import D4.C2GroupedTensorPart05_02
import D4.C2GroupedTensorPart06_02
import D4.C2GroupedTensorPart07_02
import D4.C2GroupedTensorPart08_02
import D4.C2GroupedTensorPart09_02
import D4.C2GroupedTensorPart10_02
import D4.C2GroupedTensorPart11_02
import D4.C2GroupedTensorPart12_02
import D4.C2GroupedTensorPart13_02
import D4.C2GroupedTensorPart14_02
import D4.C2GroupedDeterminants
import D4.C2GroupedTensorPartition
import D4.CertificateBlocks228
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c2Tensor02_merge_check : sumFast [c2GroupedPart0_02,c2GroupedPart1_02,c2GroupedPart2_02,c2GroupedPart3_02,c2GroupedPart4_02,c2GroupedPart5_02,c2GroupedPart6_02,c2GroupedPart7_02,c2GroupedPart8_02,c2GroupedPart9_02,c2GroupedPart10_02,c2GroupedPart11_02,c2GroupedPart12_02,c2GroupedPart13_02,c2GroupedPart14_02] = c2Tensor02 := by kernel_rfl
theorem c2Tensor02_check :
    sumFast (c2TensorGroups.map (fun g => cellGroupedTensor c2VertexCoefficients c2Cell c2CellDetPoly g.1 g.2 0 2)) = c2Tensor02 := by
  simp only [c2TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_228]
  simpa (config := {implicitDefEqProofs := false}) only [
    c2GroupedPart0_02_raw_check,
    c2GroupedPart1_02_raw_check,
    c2GroupedPart2_02_raw_check,
    c2GroupedPart3_02_raw_check,
    c2GroupedPart4_02_raw_check,
    c2GroupedPart5_02_raw_check,
    c2GroupedPart6_02_raw_check,
    c2GroupedPart7_02_raw_check,
    c2GroupedPart8_02_raw_check,
    c2GroupedPart9_02_raw_check,
    c2GroupedPart10_02_raw_check,
    c2GroupedPart11_02_raw_check,
    c2GroupedPart12_02_raw_check,
    c2GroupedPart13_02_raw_check,
    c2GroupedPart14_02_raw_check] using c2Tensor02_merge_check

theorem c2Tensor02_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c2Tensor02 =
    ∑ t,eval (extendWeight w) (c2CellDetPoly t)*cellHessian (secondaryVertex c2VertexCoefficients w) (c2Cell t) 0 2 := by
  rw [← c2Tensor02_check]
  exact cellGroupedTensorFull_eval c2VertexCoefficients c2Cell c2CellDetPoly c2TensorGroups
    c2_group_determinants c2_tensor_groups_partition w 0 2
end
end D4.Secondary
