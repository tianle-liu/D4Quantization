import D4.C3TensorData33
import D4.C3GroupedTensorPart00_33
import D4.C3GroupedTensorPart01_33
import D4.C3GroupedTensorPart02_33
import D4.C3GroupedTensorPart03_33
import D4.C3GroupedTensorPart04_33
import D4.C3GroupedTensorPart05_33
import D4.C3GroupedTensorPart06_33
import D4.C3GroupedTensorPart07_33
import D4.C3GroupedTensorPart08_33
import D4.C3GroupedTensorPart09_33
import D4.C3GroupedTensorPart10_33
import D4.C3GroupedTensorPart11_33
import D4.C3GroupedTensorPart12_33
import D4.C3GroupedTensorPart13_33
import D4.C3GroupedTensorPart14_33
import D4.C3GroupedDeterminants
import D4.C3GroupedTensorPartition
import D4.CertificateBlocks225
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
noncomputable section
theorem c3Tensor33_merge_check : sumFast [c3GroupedPart0_33,c3GroupedPart1_33,c3GroupedPart2_33,c3GroupedPart3_33,c3GroupedPart4_33,c3GroupedPart5_33,c3GroupedPart6_33,c3GroupedPart7_33,c3GroupedPart8_33,c3GroupedPart9_33,c3GroupedPart10_33,c3GroupedPart11_33,c3GroupedPart12_33,c3GroupedPart13_33,c3GroupedPart14_33] = c3Tensor33 := by kernel_rfl
theorem c3Tensor33_check :
    sumFast (c3TensorGroups.map (fun g => cellGroupedTensor c3VertexCoefficients c3Cell c3CellDetPoly g.1 g.2 3 3)) = c3Tensor33 := by
  simp only [c3TensorGroups,List.map_cons,List.map_nil]
  rw [sumFast_blocks_225]
  simpa (config := {implicitDefEqProofs := false}) only [
    c3GroupedPart0_33_raw_check,
    c3GroupedPart1_33_raw_check,
    c3GroupedPart2_33_raw_check,
    c3GroupedPart3_33_raw_check,
    c3GroupedPart4_33_raw_check,
    c3GroupedPart5_33_raw_check,
    c3GroupedPart6_33_raw_check,
    c3GroupedPart7_33_raw_check,
    c3GroupedPart8_33_raw_check,
    c3GroupedPart9_33_raw_check,
    c3GroupedPart10_33_raw_check,
    c3GroupedPart11_33_raw_check,
    c3GroupedPart12_33_raw_check,
    c3GroupedPart13_33_raw_check,
    c3GroupedPart14_33_raw_check] using c3Tensor33_merge_check

theorem c3Tensor33_eval (w : Fin 10 → ℝ) : eval (extendWeight w) c3Tensor33 =
    ∑ t,eval (extendWeight w) (c3CellDetPoly t)*cellHessian (secondaryVertex c3VertexCoefficients w) (c3Cell t) 3 3 := by
  rw [← c3Tensor33_check]
  exact cellGroupedTensorFull_eval c3VertexCoefficients c3Cell c3CellDetPoly c3TensorGroups
    c3_group_determinants c3_tensor_groups_partition w 3 3
end
end D4.Secondary
