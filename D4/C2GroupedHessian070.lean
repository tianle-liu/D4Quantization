import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup70_det_check : c2TensorGroup70.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 94)) = true := by kernel_rfl
private def c2GroupHessian70_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 80),([0,6], 8),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 16)]
def c2GroupHessian70_00 : Poly := List.flatten [c2GroupHessian70_00Chunk0]
theorem c2GroupHessian70_00_check : sumFast (c2TensorGroup70.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian70_00 := by kernel_rfl
private def c2GroupHessian70_01Chunk0 : Poly := [([0,0], 12),([0,2], 4),([0,6], -4),([0,7], 8),([0,8], -40),([1,8], -40),([2,6], -8),([5,8], -40),([6,7], 4)]
def c2GroupHessian70_01 : Poly := List.flatten [c2GroupHessian70_01Chunk0]
theorem c2GroupHessian70_01_check : sumFast (c2TensorGroup70.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian70_01 := by kernel_rfl
private def c2GroupHessian70_02Chunk0 : Poly := [([0,0], -48),([0,1], -40),([0,3], 4),([0,5], -80),([0,6], -4),([0,7], -8),([0,9], -40),([1,5], -40),([1,9], -40),([3,6], -8),([5,5], -40),([5,9], -40),([6,7], -4)]
def c2GroupHessian70_02 : Poly := List.flatten [c2GroupHessian70_02Chunk0]
theorem c2GroupHessian70_02_check : sumFast (c2TensorGroup70.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian70_02 := by kernel_rfl
private def c2GroupHessian70_03Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -8),([0,8], 40),([0,9], 40),([1,4], 40),([1,8], 40),([1,9], 40),([4,5], 40),([5,8], 40),([5,9], 40),([6,6], -16)]
def c2GroupHessian70_03 : Poly := List.flatten [c2GroupHessian70_03Chunk0]
theorem c2GroupHessian70_03_check : sumFast (c2TensorGroup70.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian70_03 := by kernel_rfl
private def c2GroupHessian70_11Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,7], 24),([2,2], 16),([2,7], 8),([7,7], 8),([8,8], 40)]
def c2GroupHessian70_11 : Poly := List.flatten [c2GroupHessian70_11Chunk0]
theorem c2GroupHessian70_11_check : sumFast (c2TensorGroup70.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian70_11 := by kernel_rfl
private def c2GroupHessian70_12Chunk0 : Poly := [([0,0], -12),([0,2], -4),([0,3], 20),([0,7], -20),([0,8], 40),([2,3], 16),([2,7], -4),([3,7], 4),([5,8], 40),([7,7], -8),([8,9], 40)]
def c2GroupHessian70_12 : Poly := List.flatten [c2GroupHessian70_12Chunk0]
theorem c2GroupHessian70_12_check : sumFast (c2TensorGroup70.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian70_12 := by kernel_rfl
private def c2GroupHessian70_13Chunk0 : Poly := [([0,0], -12),([0,2], -4),([0,6], 4),([0,7], -8),([0,8], -40),([2,6], 8),([4,8], -40),([6,7], -4),([8,8], -40),([8,9], -40)]
def c2GroupHessian70_13 : Poly := List.flatten [c2GroupHessian70_13Chunk0]
theorem c2GroupHessian70_13_check : sumFast (c2TensorGroup70.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian70_13 := by kernel_rfl
private def c2GroupHessian70_22Chunk0 : Poly := [([0,0], 48),([0,3], -8),([0,5], 80),([0,7], 16),([0,9], 80),([3,3], 16),([3,7], -8),([5,5], 40),([5,9], 80),([7,7], 8),([9,9], 40)]
def c2GroupHessian70_22 : Poly := List.flatten [c2GroupHessian70_22Chunk0]
theorem c2GroupHessian70_22_check : sumFast (c2TensorGroup70.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian70_22 := by kernel_rfl
private def c2GroupHessian70_23Chunk0 : Poly := [([0,0], -32),([0,3], -4),([0,4], -40),([0,5], -40),([0,6], 4),([0,7], 8),([0,8], -40),([0,9], -80),([3,6], 8),([4,5], -40),([4,9], -40),([5,8], -40),([5,9], -40),([6,7], 4),([8,9], -40),([9,9], -40)]
def c2GroupHessian70_23 : Poly := List.flatten [c2GroupHessian70_23Chunk0]
theorem c2GroupHessian70_23_check : sumFast (c2TensorGroup70.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian70_23 := by kernel_rfl
private def c2GroupHessian70_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 8),([0,8], 80),([0,9], 80),([4,4], 40),([4,8], 80),([4,9], 80),([6,6], 16),([8,8], 40),([8,9], 80),([9,9], 40)]
def c2GroupHessian70_33 : Poly := List.flatten [c2GroupHessian70_33Chunk0]
theorem c2GroupHessian70_33_check : sumFast (c2TensorGroup70.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian70_33 := by kernel_rfl
end D4.Secondary
