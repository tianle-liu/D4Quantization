import D4.C3TensorData12
import D4.C3GroupedTensorPart00_12
import D4.C3GroupedTensorPart01_12
import D4.C3GroupedTensorPart02_12
import D4.C3GroupedTensorPart03_12
import D4.C3GroupedTensorPart04_12
import D4.C3GroupedTensorPart05_12
import D4.C3GroupedTensorPart06_12
import D4.C3GroupedTensorPart07_12
import D4.C3GroupedTensorPart08_12
import D4.C3GroupedTensorPart09_12
import D4.C3GroupedTensorPart10_12
import D4.C3GroupedTensorPart11_12
import D4.C3GroupedTensorPart12_12
import D4.C3GroupedTensorPart13_12
import D4.C3GroupedTensorPart14_12
import D4.C3GroupedDeterminants
import D4.C3GroupedTensorPartition
import D4.CertificateBlocks225
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c3Tensor12_merge_check : sumFast [c3GroupedPart0_12,c3GroupedPart1_12,c3GroupedPart2_12,c3GroupedPart3_12,c3GroupedPart4_12,c3GroupedPart5_12,c3GroupedPart6_12,c3GroupedPart7_12,c3GroupedPart8_12,c3GroupedPart9_12,c3GroupedPart10_12,c3GroupedPart11_12,c3GroupedPart12_12,c3GroupedPart13_12,c3GroupedPart14_12] = c3Tensor12 := by kernel_rfl
theorem c3Tensor12_check :
    sumFast (c3TensorGroups.map (fun g => cellGroupedTensor c3VertexCoefficients c3Cell c3CellDetPoly g.1 g.2 1 2)) = c3Tensor12 := by
  simp only [c3TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_225]
  simpa (config := {implicitDefEqProofs := false}) only [
    c3GroupedPart0_12_raw_check,
    c3GroupedPart1_12_raw_check,
    c3GroupedPart2_12_raw_check,
    c3GroupedPart3_12_raw_check,
    c3GroupedPart4_12_raw_check,
    c3GroupedPart5_12_raw_check,
    c3GroupedPart6_12_raw_check,
    c3GroupedPart7_12_raw_check,
    c3GroupedPart8_12_raw_check,
    c3GroupedPart9_12_raw_check,
    c3GroupedPart10_12_raw_check,
    c3GroupedPart11_12_raw_check,
    c3GroupedPart12_12_raw_check,
    c3GroupedPart13_12_raw_check,
    c3GroupedPart14_12_raw_check] using c3Tensor12_merge_check

theorem c3Tensor12_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c3Tensor12 =
    ∑ t,eval (extendWeight w) (c3CellDetPoly t)*cellHessian (secondaryVertex c3VertexCoefficients w) (c3Cell t) 1 2 := by
  rw [← c3Tensor12_check]
  exact cellGroupedTensorFull_eval c3VertexCoefficients c3Cell c3CellDetPoly c3TensorGroups
    c3_group_determinants c3_tensor_groups_partition w 1 2
end
end D4.Secondary
