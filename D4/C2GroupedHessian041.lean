import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup41_det_check : c2TensorGroup41.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 59)) = true := by kernel_rfl
private def c2GroupHessian41_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 8),([0,6], 80),([1,1], 40),([1,6], 80),([5,5], 16),([6,6], 40)]
def c2GroupHessian41_00 : Poly := List.flatten [c2GroupHessian41_00Chunk0]
theorem c2GroupHessian41_00_check : sumFast (c2TensorGroup41.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian41_00 := by kernel_rfl
private def c2GroupHessian41_01Chunk0 : Poly := [([0,0], 12),([0,2], 8),([0,5], -4),([0,7], -40),([0,8], 4),([1,7], -40),([2,5], 4),([5,8], -8),([6,7], -40)]
def c2GroupHessian41_01 : Poly := List.flatten [c2GroupHessian41_01Chunk0]
theorem c2GroupHessian41_01_check : sumFast (c2TensorGroup41.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian41_01 := by kernel_rfl
private def c2GroupHessian41_02Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,3], 40),([0,5], -8),([0,6], 40),([0,7], 40),([0,9], 40),([1,3], 40),([1,7], 40),([1,9], 40),([3,6], 40),([5,5], -16),([6,7], 40),([6,9], 40)]
def c2GroupHessian41_02 : Poly := List.flatten [c2GroupHessian41_02Chunk0]
theorem c2GroupHessian41_02_check : sumFast (c2TensorGroup41.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian41_02 := by kernel_rfl
private def c2GroupHessian41_03Chunk0 : Poly := [([0,0], -44),([0,1], -40),([0,5], 8),([0,6], -80),([0,8], -4),([0,9], -40),([1,6], -40),([1,9], -40),([4,5], 20),([5,8], 8),([6,6], -40),([6,9], -40)]
def c2GroupHessian41_03 : Poly := List.flatten [c2GroupHessian41_03Chunk0]
theorem c2GroupHessian41_03_check : sumFast (c2TensorGroup41.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian41_03 := by kernel_rfl
private def c2GroupHessian41_11Chunk0 : Poly := [([0,0], 32),([0,2], 24),([0,8], 40),([2,2], 8),([2,8], 8),([7,7], 40),([8,8], 16)]
def c2GroupHessian41_11 : Poly := List.flatten [c2GroupHessian41_11Chunk0]
theorem c2GroupHessian41_11_check : sumFast (c2TensorGroup41.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian41_11 := by kernel_rfl
private def c2GroupHessian41_12Chunk0 : Poly := [([0,0], -12),([0,2], -8),([0,5], 4),([0,7], -40),([0,8], -4),([2,5], -4),([3,7], -40),([5,8], 8),([7,7], -40),([7,9], -40)]
def c2GroupHessian41_12 : Poly := List.flatten [c2GroupHessian41_12Chunk0]
theorem c2GroupHessian41_12_check : sumFast (c2TensorGroup41.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian41_12 := by kernel_rfl
private def c2GroupHessian41_13Chunk0 : Poly := [([0,0], -20),([0,2], -4),([0,4], -20),([0,7], 40),([0,8], -36),([2,8], -4),([4,8], -20),([6,7], 40),([7,9], 40),([8,8], -16)]
def c2GroupHessian41_13 : Poly := List.flatten [c2GroupHessian41_13Chunk0]
theorem c2GroupHessian41_13_check : sumFast (c2TensorGroup41.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian41_13 := by kernel_rfl
private def c2GroupHessian41_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 8),([0,7], 80),([0,9], 80),([3,3], 40),([3,7], 80),([3,9], 80),([5,5], 16),([7,7], 40),([7,9], 80),([9,9], 40)]
def c2GroupHessian41_22 : Poly := List.flatten [c2GroupHessian41_22Chunk0]
theorem c2GroupHessian41_22_check : sumFast (c2TensorGroup41.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian41_22 := by kernel_rfl
private def c2GroupHessian41_23Chunk0 : Poly := [([0,0], -36),([0,3], -40),([0,5], -8),([0,6], -40),([0,7], -40),([0,8], 4),([0,9], -80),([3,6], -40),([3,9], -40),([4,5], -20),([5,8], -8),([6,7], -40),([6,9], -40),([7,9], -40),([9,9], -40)]
def c2GroupHessian41_23 : Poly := List.flatten [c2GroupHessian41_23Chunk0]
theorem c2GroupHessian41_23_check : sumFast (c2TensorGroup41.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian41_23 := by kernel_rfl
private def c2GroupHessian41_33Chunk0 : Poly := [([0,0], 56),([0,4], 40),([0,6], 80),([0,8], 32),([0,9], 80),([4,4], 40),([4,8], 40),([6,6], 40),([6,9], 80),([8,8], 16),([9,9], 40)]
def c2GroupHessian41_33 : Poly := List.flatten [c2GroupHessian41_33Chunk0]
theorem c2GroupHessian41_33_check : sumFast (c2TensorGroup41.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian41_33 := by kernel_rfl
end D4.Secondary
