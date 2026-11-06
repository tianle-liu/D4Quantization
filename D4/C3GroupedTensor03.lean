import D4.C3TensorData03
import D4.C3GroupedTensorPart00_03
import D4.C3GroupedTensorPart01_03
import D4.C3GroupedTensorPart02_03
import D4.C3GroupedTensorPart03_03
import D4.C3GroupedTensorPart04_03
import D4.C3GroupedTensorPart05_03
import D4.C3GroupedTensorPart06_03
import D4.C3GroupedTensorPart07_03
import D4.C3GroupedTensorPart08_03
import D4.C3GroupedTensorPart09_03
import D4.C3GroupedTensorPart10_03
import D4.C3GroupedTensorPart11_03
import D4.C3GroupedTensorPart12_03
import D4.C3GroupedTensorPart13_03
import D4.C3GroupedTensorPart14_03
import D4.C3GroupedDeterminants
import D4.C3GroupedTensorPartition
import D4.CertificateBlocks225
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c3Tensor03_merge_check : sumFast [c3GroupedPart0_03,c3GroupedPart1_03,c3GroupedPart2_03,c3GroupedPart3_03,c3GroupedPart4_03,c3GroupedPart5_03,c3GroupedPart6_03,c3GroupedPart7_03,c3GroupedPart8_03,c3GroupedPart9_03,c3GroupedPart10_03,c3GroupedPart11_03,c3GroupedPart12_03,c3GroupedPart13_03,c3GroupedPart14_03] = c3Tensor03 := by kernel_rfl
theorem c3Tensor03_check :
    sumFast (c3TensorGroups.map (fun g => cellGroupedTensor c3VertexCoefficients c3Cell c3CellDetPoly g.1 g.2 0 3)) = c3Tensor03 := by
  simp only [c3TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_225]
  simpa (config := {implicitDefEqProofs := false}) only [
    c3GroupedPart0_03_raw_check,
    c3GroupedPart1_03_raw_check,
    c3GroupedPart2_03_raw_check,
    c3GroupedPart3_03_raw_check,
    c3GroupedPart4_03_raw_check,
    c3GroupedPart5_03_raw_check,
    c3GroupedPart6_03_raw_check,
    c3GroupedPart7_03_raw_check,
    c3GroupedPart8_03_raw_check,
    c3GroupedPart9_03_raw_check,
    c3GroupedPart10_03_raw_check,
    c3GroupedPart11_03_raw_check,
    c3GroupedPart12_03_raw_check,
    c3GroupedPart13_03_raw_check,
    c3GroupedPart14_03_raw_check] using c3Tensor03_merge_check

theorem c3Tensor03_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c3Tensor03 =
    ∑ t,eval (extendWeight w) (c3CellDetPoly t)*cellHessian (secondaryVertex c3VertexCoefficients w) (c3Cell t) 0 3 := by
  rw [← c3Tensor03_check]
  exact cellGroupedTensorFull_eval c3VertexCoefficients c3Cell c3CellDetPoly c3TensorGroups
    c3_group_determinants c3_tensor_groups_partition w 0 3
end
end D4.Secondary
