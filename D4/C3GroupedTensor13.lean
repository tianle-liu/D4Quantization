import D4.C3TensorData13
import D4.C3GroupedTensorPart00_13
import D4.C3GroupedTensorPart01_13
import D4.C3GroupedTensorPart02_13
import D4.C3GroupedTensorPart03_13
import D4.C3GroupedTensorPart04_13
import D4.C3GroupedTensorPart05_13
import D4.C3GroupedTensorPart06_13
import D4.C3GroupedTensorPart07_13
import D4.C3GroupedTensorPart08_13
import D4.C3GroupedTensorPart09_13
import D4.C3GroupedTensorPart10_13
import D4.C3GroupedTensorPart11_13
import D4.C3GroupedTensorPart12_13
import D4.C3GroupedTensorPart13_13
import D4.C3GroupedTensorPart14_13
import D4.C3GroupedDeterminants
import D4.C3GroupedTensorPartition
import D4.CertificateBlocks225
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c3Tensor13_merge_check : sumFast [c3GroupedPart0_13,c3GroupedPart1_13,c3GroupedPart2_13,c3GroupedPart3_13,c3GroupedPart4_13,c3GroupedPart5_13,c3GroupedPart6_13,c3GroupedPart7_13,c3GroupedPart8_13,c3GroupedPart9_13,c3GroupedPart10_13,c3GroupedPart11_13,c3GroupedPart12_13,c3GroupedPart13_13,c3GroupedPart14_13] = c3Tensor13 := by kernel_rfl
theorem c3Tensor13_check :
    sumFast (c3TensorGroups.map (fun g => cellGroupedTensor c3VertexCoefficients c3Cell c3CellDetPoly g.1 g.2 1 3)) = c3Tensor13 := by
  simp only [c3TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_225]
  simpa (config := {implicitDefEqProofs := false}) only [
    c3GroupedPart0_13_raw_check,
    c3GroupedPart1_13_raw_check,
    c3GroupedPart2_13_raw_check,
    c3GroupedPart3_13_raw_check,
    c3GroupedPart4_13_raw_check,
    c3GroupedPart5_13_raw_check,
    c3GroupedPart6_13_raw_check,
    c3GroupedPart7_13_raw_check,
    c3GroupedPart8_13_raw_check,
    c3GroupedPart9_13_raw_check,
    c3GroupedPart10_13_raw_check,
    c3GroupedPart11_13_raw_check,
    c3GroupedPart12_13_raw_check,
    c3GroupedPart13_13_raw_check,
    c3GroupedPart14_13_raw_check] using c3Tensor13_merge_check

theorem c3Tensor13_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c3Tensor13 =
    ∑ t,eval (extendWeight w) (c3CellDetPoly t)*cellHessian (secondaryVertex c3VertexCoefficients w) (c3Cell t) 1 3 := by
  rw [← c3Tensor13_check]
  exact cellGroupedTensorFull_eval c3VertexCoefficients c3Cell c3CellDetPoly c3TensorGroups
    c3_group_determinants c3_tensor_groups_partition w 1 3
end
end D4.Secondary
