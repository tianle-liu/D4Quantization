import D4.C3TensorData00
import D4.C3GroupedTensorPart00_00
import D4.C3GroupedTensorPart01_00
import D4.C3GroupedTensorPart02_00
import D4.C3GroupedTensorPart03_00
import D4.C3GroupedTensorPart04_00
import D4.C3GroupedTensorPart05_00
import D4.C3GroupedTensorPart06_00
import D4.C3GroupedTensorPart07_00
import D4.C3GroupedTensorPart08_00
import D4.C3GroupedTensorPart09_00
import D4.C3GroupedTensorPart10_00
import D4.C3GroupedTensorPart11_00
import D4.C3GroupedTensorPart12_00
import D4.C3GroupedTensorPart13_00
import D4.C3GroupedTensorPart14_00
import D4.C3GroupedDeterminants
import D4.C3GroupedTensorPartition
import D4.CertificateBlocks225
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c3Tensor00_merge_check : sumFast [c3GroupedPart0_00,c3GroupedPart1_00,c3GroupedPart2_00,c3GroupedPart3_00,c3GroupedPart4_00,c3GroupedPart5_00,c3GroupedPart6_00,c3GroupedPart7_00,c3GroupedPart8_00,c3GroupedPart9_00,c3GroupedPart10_00,c3GroupedPart11_00,c3GroupedPart12_00,c3GroupedPart13_00,c3GroupedPart14_00] = c3Tensor00 := by kernel_rfl
theorem c3Tensor00_check :
    sumFast (c3TensorGroups.map (fun g => cellGroupedTensor c3VertexCoefficients c3Cell c3CellDetPoly g.1 g.2 0 0)) = c3Tensor00 := by
  simp only [c3TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_225]
  simpa (config := {implicitDefEqProofs := false}) only [
    c3GroupedPart0_00_raw_check,
    c3GroupedPart1_00_raw_check,
    c3GroupedPart2_00_raw_check,
    c3GroupedPart3_00_raw_check,
    c3GroupedPart4_00_raw_check,
    c3GroupedPart5_00_raw_check,
    c3GroupedPart6_00_raw_check,
    c3GroupedPart7_00_raw_check,
    c3GroupedPart8_00_raw_check,
    c3GroupedPart9_00_raw_check,
    c3GroupedPart10_00_raw_check,
    c3GroupedPart11_00_raw_check,
    c3GroupedPart12_00_raw_check,
    c3GroupedPart13_00_raw_check,
    c3GroupedPart14_00_raw_check] using c3Tensor00_merge_check

theorem c3Tensor00_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c3Tensor00 =
    ∑ t,eval (extendWeight w) (c3CellDetPoly t)*cellHessian (secondaryVertex c3VertexCoefficients w) (c3Cell t) 0 0 := by
  rw [← c3Tensor00_check]
  exact cellGroupedTensorFull_eval c3VertexCoefficients c3Cell c3CellDetPoly c3TensorGroups
    c3_group_determinants c3_tensor_groups_partition w 0 0
end
end D4.Secondary
