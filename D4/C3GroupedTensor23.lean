import D4.C3TensorData23
import D4.C3GroupedTensorPart00_23
import D4.C3GroupedTensorPart01_23
import D4.C3GroupedTensorPart02_23
import D4.C3GroupedTensorPart03_23
import D4.C3GroupedTensorPart04_23
import D4.C3GroupedTensorPart05_23
import D4.C3GroupedTensorPart06_23
import D4.C3GroupedTensorPart07_23
import D4.C3GroupedTensorPart08_23
import D4.C3GroupedTensorPart09_23
import D4.C3GroupedTensorPart10_23
import D4.C3GroupedTensorPart11_23
import D4.C3GroupedTensorPart12_23
import D4.C3GroupedTensorPart13_23
import D4.C3GroupedTensorPart14_23
import D4.C3GroupedDeterminants
import D4.C3GroupedTensorPartition
import D4.CertificateBlocks225
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c3Tensor23_merge_check : sumFast [c3GroupedPart0_23,c3GroupedPart1_23,c3GroupedPart2_23,c3GroupedPart3_23,c3GroupedPart4_23,c3GroupedPart5_23,c3GroupedPart6_23,c3GroupedPart7_23,c3GroupedPart8_23,c3GroupedPart9_23,c3GroupedPart10_23,c3GroupedPart11_23,c3GroupedPart12_23,c3GroupedPart13_23,c3GroupedPart14_23] = c3Tensor23 := by kernel_rfl
theorem c3Tensor23_check :
    sumFast (c3TensorGroups.map (fun g => cellGroupedTensor c3VertexCoefficients c3Cell c3CellDetPoly g.1 g.2 2 3)) = c3Tensor23 := by
  simp only [c3TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_225]
  simpa (config := {implicitDefEqProofs := false}) only [
    c3GroupedPart0_23_raw_check,
    c3GroupedPart1_23_raw_check,
    c3GroupedPart2_23_raw_check,
    c3GroupedPart3_23_raw_check,
    c3GroupedPart4_23_raw_check,
    c3GroupedPart5_23_raw_check,
    c3GroupedPart6_23_raw_check,
    c3GroupedPart7_23_raw_check,
    c3GroupedPart8_23_raw_check,
    c3GroupedPart9_23_raw_check,
    c3GroupedPart10_23_raw_check,
    c3GroupedPart11_23_raw_check,
    c3GroupedPart12_23_raw_check,
    c3GroupedPart13_23_raw_check,
    c3GroupedPart14_23_raw_check] using c3Tensor23_merge_check

theorem c3Tensor23_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c3Tensor23 =
    ∑ t,eval (extendWeight w) (c3CellDetPoly t)*cellHessian (secondaryVertex c3VertexCoefficients w) (c3Cell t) 2 3 := by
  rw [← c3Tensor23_check]
  exact cellGroupedTensorFull_eval c3VertexCoefficients c3Cell c3CellDetPoly c3TensorGroups
    c3_group_determinants c3_tensor_groups_partition w 2 3
end
end D4.Secondary
