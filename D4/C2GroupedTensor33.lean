import D4.C2TensorData33
import D4.C2GroupedTensorPart00_33
import D4.C2GroupedTensorPart01_33
import D4.C2GroupedTensorPart02_33
import D4.C2GroupedTensorPart03_33
import D4.C2GroupedTensorPart04_33
import D4.C2GroupedTensorPart05_33
import D4.C2GroupedTensorPart06_33
import D4.C2GroupedTensorPart07_33
import D4.C2GroupedTensorPart08_33
import D4.C2GroupedTensorPart09_33
import D4.C2GroupedTensorPart10_33
import D4.C2GroupedTensorPart11_33
import D4.C2GroupedTensorPart12_33
import D4.C2GroupedTensorPart13_33
import D4.C2GroupedTensorPart14_33
import D4.C2GroupedDeterminants
import D4.C2GroupedTensorPartition
import D4.CertificateBlocks228
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c2Tensor33_merge_check : sumFast [c2GroupedPart0_33,c2GroupedPart1_33,c2GroupedPart2_33,c2GroupedPart3_33,c2GroupedPart4_33,c2GroupedPart5_33,c2GroupedPart6_33,c2GroupedPart7_33,c2GroupedPart8_33,c2GroupedPart9_33,c2GroupedPart10_33,c2GroupedPart11_33,c2GroupedPart12_33,c2GroupedPart13_33,c2GroupedPart14_33] = c2Tensor33 := by kernel_rfl
theorem c2Tensor33_check :
    sumFast (c2TensorGroups.map (fun g => cellGroupedTensor c2VertexCoefficients c2Cell c2CellDetPoly g.1 g.2 3 3)) = c2Tensor33 := by
  simp only [c2TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_228]
  simpa (config := {implicitDefEqProofs := false}) only [
    c2GroupedPart0_33_raw_check,
    c2GroupedPart1_33_raw_check,
    c2GroupedPart2_33_raw_check,
    c2GroupedPart3_33_raw_check,
    c2GroupedPart4_33_raw_check,
    c2GroupedPart5_33_raw_check,
    c2GroupedPart6_33_raw_check,
    c2GroupedPart7_33_raw_check,
    c2GroupedPart8_33_raw_check,
    c2GroupedPart9_33_raw_check,
    c2GroupedPart10_33_raw_check,
    c2GroupedPart11_33_raw_check,
    c2GroupedPart12_33_raw_check,
    c2GroupedPart13_33_raw_check,
    c2GroupedPart14_33_raw_check] using c2Tensor33_merge_check

theorem c2Tensor33_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c2Tensor33 =
    ∑ t,eval (extendWeight w) (c2CellDetPoly t)*cellHessian (secondaryVertex c2VertexCoefficients w) (c2Cell t) 3 3 := by
  rw [← c2Tensor33_check]
  exact cellGroupedTensorFull_eval c2VertexCoefficients c2Cell c2CellDetPoly c2TensorGroups
    c2_group_determinants c2_tensor_groups_partition w 3 3
end
end D4.Secondary
