import D4.C3TensorData02
import D4.C3GroupedTensorPart00_02
import D4.C3GroupedTensorPart01_02
import D4.C3GroupedTensorPart02_02
import D4.C3GroupedTensorPart03_02
import D4.C3GroupedTensorPart04_02
import D4.C3GroupedTensorPart05_02
import D4.C3GroupedTensorPart06_02
import D4.C3GroupedTensorPart07_02
import D4.C3GroupedTensorPart08_02
import D4.C3GroupedTensorPart09_02
import D4.C3GroupedTensorPart10_02
import D4.C3GroupedTensorPart11_02
import D4.C3GroupedTensorPart12_02
import D4.C3GroupedTensorPart13_02
import D4.C3GroupedTensorPart14_02
import D4.C3GroupedDeterminants
import D4.C3GroupedTensorPartition
import D4.CertificateBlocks225
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c3Tensor02_merge_check : sumFast [c3GroupedPart0_02,c3GroupedPart1_02,c3GroupedPart2_02,c3GroupedPart3_02,c3GroupedPart4_02,c3GroupedPart5_02,c3GroupedPart6_02,c3GroupedPart7_02,c3GroupedPart8_02,c3GroupedPart9_02,c3GroupedPart10_02,c3GroupedPart11_02,c3GroupedPart12_02,c3GroupedPart13_02,c3GroupedPart14_02] = c3Tensor02 := by kernel_rfl
theorem c3Tensor02_check :
    sumFast (c3TensorGroups.map (fun g => cellGroupedTensor c3VertexCoefficients c3Cell c3CellDetPoly g.1 g.2 0 2)) = c3Tensor02 := by
  simp only [c3TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_225]
  simpa (config := {implicitDefEqProofs := false}) only [
    c3GroupedPart0_02_raw_check,
    c3GroupedPart1_02_raw_check,
    c3GroupedPart2_02_raw_check,
    c3GroupedPart3_02_raw_check,
    c3GroupedPart4_02_raw_check,
    c3GroupedPart5_02_raw_check,
    c3GroupedPart6_02_raw_check,
    c3GroupedPart7_02_raw_check,
    c3GroupedPart8_02_raw_check,
    c3GroupedPart9_02_raw_check,
    c3GroupedPart10_02_raw_check,
    c3GroupedPart11_02_raw_check,
    c3GroupedPart12_02_raw_check,
    c3GroupedPart13_02_raw_check,
    c3GroupedPart14_02_raw_check] using c3Tensor02_merge_check

theorem c3Tensor02_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c3Tensor02 =
    ∑ t,eval (extendWeight w) (c3CellDetPoly t)*cellHessian (secondaryVertex c3VertexCoefficients w) (c3Cell t) 0 2 := by
  rw [← c3Tensor02_check]
  exact cellGroupedTensorFull_eval c3VertexCoefficients c3Cell c3CellDetPoly c3TensorGroups
    c3_group_determinants c3_tensor_groups_partition w 0 2
end
end D4.Secondary
