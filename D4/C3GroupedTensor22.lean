import D4.C3TensorData22
import D4.C3GroupedTensorPart00_22
import D4.C3GroupedTensorPart01_22
import D4.C3GroupedTensorPart02_22
import D4.C3GroupedTensorPart03_22
import D4.C3GroupedTensorPart04_22
import D4.C3GroupedTensorPart05_22
import D4.C3GroupedTensorPart06_22
import D4.C3GroupedTensorPart07_22
import D4.C3GroupedTensorPart08_22
import D4.C3GroupedTensorPart09_22
import D4.C3GroupedTensorPart10_22
import D4.C3GroupedTensorPart11_22
import D4.C3GroupedTensorPart12_22
import D4.C3GroupedTensorPart13_22
import D4.C3GroupedTensorPart14_22
import D4.C3GroupedDeterminants
import D4.C3GroupedTensorPartition
import D4.CertificateBlocks225
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c3Tensor22_merge_check : sumFast [c3GroupedPart0_22,c3GroupedPart1_22,c3GroupedPart2_22,c3GroupedPart3_22,c3GroupedPart4_22,c3GroupedPart5_22,c3GroupedPart6_22,c3GroupedPart7_22,c3GroupedPart8_22,c3GroupedPart9_22,c3GroupedPart10_22,c3GroupedPart11_22,c3GroupedPart12_22,c3GroupedPart13_22,c3GroupedPart14_22] = c3Tensor22 := by kernel_rfl
theorem c3Tensor22_check :
    sumFast (c3TensorGroups.map (fun g => cellGroupedTensor c3VertexCoefficients c3Cell c3CellDetPoly g.1 g.2 2 2)) = c3Tensor22 := by
  simp only [c3TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_225]
  simpa (config := {implicitDefEqProofs := false}) only [
    c3GroupedPart0_22_raw_check,
    c3GroupedPart1_22_raw_check,
    c3GroupedPart2_22_raw_check,
    c3GroupedPart3_22_raw_check,
    c3GroupedPart4_22_raw_check,
    c3GroupedPart5_22_raw_check,
    c3GroupedPart6_22_raw_check,
    c3GroupedPart7_22_raw_check,
    c3GroupedPart8_22_raw_check,
    c3GroupedPart9_22_raw_check,
    c3GroupedPart10_22_raw_check,
    c3GroupedPart11_22_raw_check,
    c3GroupedPart12_22_raw_check,
    c3GroupedPart13_22_raw_check,
    c3GroupedPart14_22_raw_check] using c3Tensor22_merge_check

theorem c3Tensor22_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c3Tensor22 =
    ∑ t,eval (extendWeight w) (c3CellDetPoly t)*cellHessian (secondaryVertex c3VertexCoefficients w) (c3Cell t) 2 2 := by
  rw [← c3Tensor22_check]
  exact cellGroupedTensorFull_eval c3VertexCoefficients c3Cell c3CellDetPoly c3TensorGroups
    c3_group_determinants c3_tensor_groups_partition w 2 2
end
end D4.Secondary
