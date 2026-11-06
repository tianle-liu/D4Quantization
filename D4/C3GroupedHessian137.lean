import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup137_det_check : c3TensorGroup137.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 179)) = true := by kernel_rfl
private def c3GroupHessian137_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 80),([0,9], 16),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 40),([9,9], 8)]
def c3GroupHessian137_00 : Poly := List.flatten [c3GroupHessian137_00Chunk0]
theorem c3GroupHessian137_00_check : sumFast (c3TensorGroup137.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian137_00 := by kernel_rfl
private def c3GroupHessian137_01Chunk0 : Poly := [([0,0], 8),([0,6], -40),([0,8], -16),([0,9], 16),([1,8], -20),([2,6], -40),([5,8], -20),([6,7], -40),([8,9], 4),([9,9], 8)]
def c3GroupHessian137_01 : Poly := List.flatten [c3GroupHessian137_01Chunk0]
theorem c3GroupHessian137_01_check : sumFast (c3TensorGroup137.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian137_01 := by kernel_rfl
private def c3GroupHessian137_02Chunk0 : Poly := [([0,0], -24),([0,1], -20),([0,3], 24),([0,5], -60),([0,6], 40),([0,9], -12),([1,3], 20),([1,5], -40),([3,5], 20),([3,9], 4),([5,5], -40),([6,7], 40),([9,9], -8)]
def c3GroupHessian137_02 : Poly := List.flatten [c3GroupHessian137_02Chunk0]
theorem c3GroupHessian137_02_check : sumFast (c3TensorGroup137.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian137_02 := by kernel_rfl
private def c3GroupHessian137_03Chunk0 : Poly := [([0,0], -8),([0,6], -40),([0,8], 16),([0,9], -16),([1,8], 20),([4,6], -40),([5,8], 20),([6,6], -40),([8,9], -4),([9,9], -8)]
def c3GroupHessian137_03 : Poly := List.flatten [c3GroupHessian137_03Chunk0]
theorem c3GroupHessian137_03_check : sumFast (c3TensorGroup137.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian137_03 := by kernel_rfl
private def c3GroupHessian137_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 80),([0,8], 8),([0,9], 16),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 16),([8,9], 8),([9,9], 8)]
def c3GroupHessian137_11 : Poly := List.flatten [c3GroupHessian137_11Chunk0]
theorem c3GroupHessian137_11_check : sumFast (c3TensorGroup137.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian137_11 := by kernel_rfl
private def c3GroupHessian137_12Chunk0 : Poly := [([0,0], -44),([0,2], -40),([0,3], 4),([0,7], -80),([0,8], 8),([0,9], -12),([2,7], -40),([3,8], -8),([3,9], 4),([5,8], 20),([7,7], -40),([8,9], -4),([9,9], -8)]
def c3GroupHessian137_12 : Poly := List.flatten [c3GroupHessian137_12Chunk0]
theorem c3GroupHessian137_12_check : sumFast (c3TensorGroup137.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian137_12 := by kernel_rfl
private def c3GroupHessian137_13Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -8),([0,9], -16),([2,4], 40),([2,6], 40),([4,7], 40),([6,7], 40),([8,8], -16),([8,9], -8),([9,9], -8)]
def c3GroupHessian137_13 : Poly := List.flatten [c3GroupHessian137_13Chunk0]
theorem c3GroupHessian137_13_check : sumFast (c3TensorGroup137.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian137_13 := by kernel_rfl
private def c3GroupHessian137_22Chunk0 : Poly := [([0,0], 56),([0,3], -16),([0,5], 40),([0,7], 80),([0,9], 8),([3,3], 16),([3,5], -40),([3,9], -8),([5,5], 40),([7,7], 40),([9,9], 8)]
def c3GroupHessian137_22 : Poly := List.flatten [c3GroupHessian137_22Chunk0]
theorem c3GroupHessian137_22_check : sumFast (c3TensorGroup137.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian137_22 := by kernel_rfl
private def c3GroupHessian137_23Chunk0 : Poly := [([0,0], -36),([0,3], -4),([0,4], -40),([0,6], -40),([0,7], -40),([0,8], -8),([0,9], 12),([3,8], 8),([3,9], -4),([4,7], -40),([5,8], -20),([6,7], -40),([8,9], 4),([9,9], 8)]
def c3GroupHessian137_23 : Poly := List.flatten [c3GroupHessian137_23Chunk0]
theorem c3GroupHessian137_23_check : sumFast (c3TensorGroup137.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian137_23 := by kernel_rfl
private def c3GroupHessian137_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 80),([0,8], 8),([0,9], 16),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 16),([8,9], 8),([9,9], 8)]
def c3GroupHessian137_33 : Poly := List.flatten [c3GroupHessian137_33Chunk0]
theorem c3GroupHessian137_33_check : sumFast (c3TensorGroup137.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian137_33 := by kernel_rfl
end D4.Secondary
