import D4.C2GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c2TensorGroup166_det_check : c2TensorGroup166.all (fun t => decide (c2CellDetPoly t = c2CellDetPoly 209)) = true := by kernel_rfl
private def c2GroupHessian166_00Chunk0 : Poly := [([0,0], 48),([0,1], 16),([0,5], 8),([0,6], 8),([1,1], 8),([1,5], 8),([1,6], 8),([5,5], 16),([5,6], -16),([6,6], 16)]
def c2GroupHessian166_00 : Poly := List.flatten [c2GroupHessian166_00Chunk0]
theorem c2GroupHessian166_00_check : sumFast (c2TensorGroup166.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 0)) = c2GroupHessian166_00 := by kernel_rfl
private def c2GroupHessian166_01Chunk0 : Poly := [([0,0], 80),([0,2], 40),([0,7], 40),([0,8], 40)]
def c2GroupHessian166_01 : Poly := List.flatten [c2GroupHessian166_01Chunk0]
theorem c2GroupHessian166_01_check : sumFast (c2TensorGroup166.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 1)) = c2GroupHessian166_01 := by kernel_rfl
private def c2GroupHessian166_02Chunk0 : Poly := [([0,0], -36),([0,1], 4),([0,3], 8),([0,5], -12),([0,6], 16),([0,7], -40),([0,9], 4),([1,3], 8),([1,5], -4),([1,9], 4),([3,5], 4),([3,6], 4),([5,5], -16),([5,6], 8),([5,9], -8),([6,9], 16)]
def c2GroupHessian166_02 : Poly := List.flatten [c2GroupHessian166_02Chunk0]
theorem c2GroupHessian166_02_check : sumFast (c2TensorGroup166.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 2)) = c2GroupHessian166_02 := by kernel_rfl
private def c2GroupHessian166_03Chunk0 : Poly := [([0,0], -44),([0,1], -4),([0,5], 8),([0,6], -20),([0,8], -40),([0,9], -4),([1,6], -4),([1,9], -4),([4,5], 20),([4,6], -20),([5,6], 8),([5,9], 8),([6,6], -16),([6,9], -16)]
def c2GroupHessian166_03 : Poly := List.flatten [c2GroupHessian166_03Chunk0]
theorem c2GroupHessian166_03_check : sumFast (c2TensorGroup166.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 0 3)) = c2GroupHessian166_03 := by kernel_rfl
private def c2GroupHessian166_11Chunk0 : Poly := [([0,0], 160),([0,2], 160),([0,7], 160),([0,8], 160),([2,2], 40),([2,7], 80),([2,8], 80),([7,7], 40),([7,8], 80),([8,8], 40)]
def c2GroupHessian166_11 : Poly := List.flatten [c2GroupHessian166_11Chunk0]
theorem c2GroupHessian166_11_check : sumFast (c2TensorGroup166.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 1)) = c2GroupHessian166_11 := by kernel_rfl
private def c2GroupHessian166_12Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -120),([0,8], -40),([2,7], -40),([7,7], -40),([7,8], -40)]
def c2GroupHessian166_12 : Poly := List.flatten [c2GroupHessian166_12Chunk0]
theorem c2GroupHessian166_12_check : sumFast (c2TensorGroup166.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 2)) = c2GroupHessian166_12 := by kernel_rfl
private def c2GroupHessian166_13Chunk0 : Poly := [([0,0], -80),([0,2], -40),([0,7], -40),([0,8], -120),([2,8], -40),([7,8], -40),([8,8], -40)]
def c2GroupHessian166_13 : Poly := List.flatten [c2GroupHessian166_13Chunk0]
theorem c2GroupHessian166_13_check : sumFast (c2TensorGroup166.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 1 3)) = c2GroupHessian166_13 := by kernel_rfl
private def c2GroupHessian166_22Chunk0 : Poly := [([0,0], 56),([0,3], 8),([0,5], 16),([0,7], 80),([0,9], 32),([3,3], 8),([3,5], -8),([3,9], 8),([5,5], 16),([5,9], 16),([7,7], 40),([9,9], 16)]
def c2GroupHessian166_22 : Poly := List.flatten [c2GroupHessian166_22Chunk0]
theorem c2GroupHessian166_22_check : sumFast (c2TensorGroup166.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 2)) = c2GroupHessian166_22 := by kernel_rfl
private def c2GroupHessian166_23Chunk0 : Poly := [([0,0], 24),([0,3], -4),([0,4], -20),([0,5], -8),([0,6], -16),([0,7], 40),([0,8], 40),([0,9], -32),([3,6], -4),([3,9], -4),([4,5], -20),([4,9], -20),([5,6], -8),([5,9], -8),([6,9], -16),([7,8], 40),([9,9], -16)]
def c2GroupHessian166_23 : Poly := List.flatten [c2GroupHessian166_23Chunk0]
theorem c2GroupHessian166_23_check : sumFast (c2TensorGroup166.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 2 3)) = c2GroupHessian166_23 := by kernel_rfl
private def c2GroupHessian166_33Chunk0 : Poly := [([0,0], 56),([0,4], 40),([0,6], 32),([0,8], 80),([0,9], 32),([4,4], 40),([4,6], 40),([4,9], 40),([6,6], 16),([6,9], 32),([8,8], 40),([9,9], 16)]
def c2GroupHessian166_33 : Poly := List.flatten [c2GroupHessian166_33Chunk0]
theorem c2GroupHessian166_33_check : sumFast (c2TensorGroup166.map (fun t => cellHessianPoly c2VertexCoefficients (c2Cell t) 3 3)) = c2GroupHessian166_33 := by kernel_rfl
end D4.Secondary
