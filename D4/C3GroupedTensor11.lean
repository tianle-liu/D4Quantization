import D4.C3TensorData11
import D4.C3GroupedTensorPart00_11
import D4.C3GroupedTensorPart01_11
import D4.C3GroupedTensorPart02_11
import D4.C3GroupedTensorPart03_11
import D4.C3GroupedTensorPart04_11
import D4.C3GroupedTensorPart05_11
import D4.C3GroupedTensorPart06_11
import D4.C3GroupedTensorPart07_11
import D4.C3GroupedTensorPart08_11
import D4.C3GroupedTensorPart09_11
import D4.C3GroupedTensorPart10_11
import D4.C3GroupedTensorPart11_11
import D4.C3GroupedTensorPart12_11
import D4.C3GroupedTensorPart13_11
import D4.C3GroupedTensorPart14_11
import D4.C3GroupedDeterminants
import D4.C3GroupedTensorPartition
import D4.CertificateBlocks225
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c3Tensor11_merge_check : sumFast [c3GroupedPart0_11,c3GroupedPart1_11,c3GroupedPart2_11,c3GroupedPart3_11,c3GroupedPart4_11,c3GroupedPart5_11,c3GroupedPart6_11,c3GroupedPart7_11,c3GroupedPart8_11,c3GroupedPart9_11,c3GroupedPart10_11,c3GroupedPart11_11,c3GroupedPart12_11,c3GroupedPart13_11,c3GroupedPart14_11] = c3Tensor11 := by kernel_rfl
theorem c3Tensor11_check :
    sumFast (c3TensorGroups.map (fun g => cellGroupedTensor c3VertexCoefficients c3Cell c3CellDetPoly g.1 g.2 1 1)) = c3Tensor11 := by
  simp only [c3TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_225]
  simpa (config := {implicitDefEqProofs := false}) only [
    c3GroupedPart0_11_raw_check,
    c3GroupedPart1_11_raw_check,
    c3GroupedPart2_11_raw_check,
    c3GroupedPart3_11_raw_check,
    c3GroupedPart4_11_raw_check,
    c3GroupedPart5_11_raw_check,
    c3GroupedPart6_11_raw_check,
    c3GroupedPart7_11_raw_check,
    c3GroupedPart8_11_raw_check,
    c3GroupedPart9_11_raw_check,
    c3GroupedPart10_11_raw_check,
    c3GroupedPart11_11_raw_check,
    c3GroupedPart12_11_raw_check,
    c3GroupedPart13_11_raw_check,
    c3GroupedPart14_11_raw_check] using c3Tensor11_merge_check

theorem c3Tensor11_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c3Tensor11 =
    ∑ t,eval (extendWeight w) (c3CellDetPoly t)*cellHessian (secondaryVertex c3VertexCoefficients w) (c3Cell t) 1 1 := by
  rw [← c3Tensor11_check]
  exact cellGroupedTensorFull_eval c3VertexCoefficients c3Cell c3CellDetPoly c3TensorGroups
    c3_group_determinants c3_tensor_groups_partition w 1 1
end
end D4.Secondary
