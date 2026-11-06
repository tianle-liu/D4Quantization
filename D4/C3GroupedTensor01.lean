import D4.C3TensorData01
import D4.C3GroupedTensorPart00_01
import D4.C3GroupedTensorPart01_01
import D4.C3GroupedTensorPart02_01
import D4.C3GroupedTensorPart03_01
import D4.C3GroupedTensorPart04_01
import D4.C3GroupedTensorPart05_01
import D4.C3GroupedTensorPart06_01
import D4.C3GroupedTensorPart07_01
import D4.C3GroupedTensorPart08_01
import D4.C3GroupedTensorPart09_01
import D4.C3GroupedTensorPart10_01
import D4.C3GroupedTensorPart11_01
import D4.C3GroupedTensorPart12_01
import D4.C3GroupedTensorPart13_01
import D4.C3GroupedTensorPart14_01
import D4.C3GroupedDeterminants
import D4.C3GroupedTensorPartition
import D4.CertificateBlocks225
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c3Tensor01_merge_check : sumFast [c3GroupedPart0_01,c3GroupedPart1_01,c3GroupedPart2_01,c3GroupedPart3_01,c3GroupedPart4_01,c3GroupedPart5_01,c3GroupedPart6_01,c3GroupedPart7_01,c3GroupedPart8_01,c3GroupedPart9_01,c3GroupedPart10_01,c3GroupedPart11_01,c3GroupedPart12_01,c3GroupedPart13_01,c3GroupedPart14_01] = c3Tensor01 := by kernel_rfl
theorem c3Tensor01_check :
    sumFast (c3TensorGroups.map (fun g => cellGroupedTensor c3VertexCoefficients c3Cell c3CellDetPoly g.1 g.2 0 1)) = c3Tensor01 := by
  simp only [c3TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_225]
  simpa (config := {implicitDefEqProofs := false}) only [
    c3GroupedPart0_01_raw_check,
    c3GroupedPart1_01_raw_check,
    c3GroupedPart2_01_raw_check,
    c3GroupedPart3_01_raw_check,
    c3GroupedPart4_01_raw_check,
    c3GroupedPart5_01_raw_check,
    c3GroupedPart6_01_raw_check,
    c3GroupedPart7_01_raw_check,
    c3GroupedPart8_01_raw_check,
    c3GroupedPart9_01_raw_check,
    c3GroupedPart10_01_raw_check,
    c3GroupedPart11_01_raw_check,
    c3GroupedPart12_01_raw_check,
    c3GroupedPart13_01_raw_check,
    c3GroupedPart14_01_raw_check] using c3Tensor01_merge_check

theorem c3Tensor01_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c3Tensor01 =
    ∑ t,eval (extendWeight w) (c3CellDetPoly t)*cellHessian (secondaryVertex c3VertexCoefficients w) (c3Cell t) 0 1 := by
  rw [← c3Tensor01_check]
  exact cellGroupedTensorFull_eval c3VertexCoefficients c3Cell c3CellDetPoly c3TensorGroups
    c3_group_determinants c3_tensor_groups_partition w 0 1
end
end D4.Secondary
