import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup45_det_check : c3TensorGroup45.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 63)) = true := by kernel_rfl
private def c3GroupHessian45_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 32),([0,6], 80),([0,9], 32),([1,1], 40),([1,6], 80),([5,5], 16),([5,9], 32),([6,6], 40),([9,9], 16)]
def c3GroupHessian45_00 : Poly := List.flatten [c3GroupHessian45_00Chunk0]
theorem c3GroupHessian45_00_check : sumFast (c3TensorGroup45.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian45_00 := by kernel_rfl
private def c3GroupHessian45_01Chunk0 : Poly := [([0,0], -4),([0,2], -8),([0,5], -4),([0,7], -40),([0,8], -20),([0,9], 12),([1,7], -40),([2,5], -8),([2,9], -8),([5,8], -20),([5,9], 16),([6,7], -40),([8,9], -20),([9,9], 16)]
def c3GroupHessian45_01 : Poly := List.flatten [c3GroupHessian45_01Chunk0]
theorem c3GroupHessian45_01_check : sumFast (c3TensorGroup45.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian45_01 := by kernel_rfl
private def c3GroupHessian45_02Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,3], 40),([0,5], -32),([0,6], 40),([0,7], 40),([0,9], -32),([1,3], 40),([1,7], 40),([3,6], 40),([5,5], -16),([5,9], -32),([6,7], 40),([9,9], -16)]
def c3GroupHessian45_02 : Poly := List.flatten [c3GroupHessian45_02Chunk0]
theorem c3GroupHessian45_02_check : sumFast (c3TensorGroup45.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian45_02 := by kernel_rfl
private def c3GroupHessian45_03Chunk0 : Poly := [([0,0], -32),([0,1], -40),([0,4], 4),([0,5], 8),([0,6], -80),([0,8], 20),([0,9], -8),([1,6], -40),([4,5], 4),([4,9], 4),([5,8], 20),([5,9], -16),([6,6], -40),([8,9], 20),([9,9], -16)]
def c3GroupHessian45_03 : Poly := List.flatten [c3GroupHessian45_03Chunk0]
theorem c3GroupHessian45_03_check : sumFast (c3TensorGroup45.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian45_03 := by kernel_rfl
private def c3GroupHessian45_11Chunk0 : Poly := [([0,0], 16),([0,2], 24),([0,8], 40),([0,9], -8),([2,2], 16),([2,8], 40),([2,9], -16),([7,7], 40),([8,8], 40),([8,9], -40),([9,9], 16)]
def c3GroupHessian45_11 : Poly := List.flatten [c3GroupHessian45_11Chunk0]
theorem c3GroupHessian45_11_check : sumFast (c3TensorGroup45.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian45_11 := by kernel_rfl
private def c3GroupHessian45_12Chunk0 : Poly := [([0,0], 4),([0,2], 8),([0,5], 4),([0,7], -40),([0,8], 20),([0,9], -12),([2,5], 8),([2,9], 8),([3,7], -40),([5,8], 20),([5,9], -16),([7,7], -40),([8,9], 20),([9,9], -16)]
def c3GroupHessian45_12 : Poly := List.flatten [c3GroupHessian45_12Chunk0]
theorem c3GroupHessian45_12_check : sumFast (c3TensorGroup45.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian45_12 := by kernel_rfl
private def c3GroupHessian45_13Chunk0 : Poly := [([0,0], -12),([0,2], -8),([0,4], 4),([0,7], 40),([0,8], -40),([0,9], 12),([2,4], 4),([2,8], -20),([2,9], 8),([4,9], 4),([6,7], 40),([8,8], -40),([8,9], 40),([9,9], -16)]
def c3GroupHessian45_13 : Poly := List.flatten [c3GroupHessian45_13Chunk0]
theorem c3GroupHessian45_13_check : sumFast (c3TensorGroup45.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian45_13 := by kernel_rfl
private def c3GroupHessian45_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 32),([0,7], 80),([0,9], 32),([3,3], 40),([3,7], 80),([5,5], 16),([5,9], 32),([7,7], 40),([9,9], 16)]
def c3GroupHessian45_22 : Poly := List.flatten [c3GroupHessian45_22Chunk0]
theorem c3GroupHessian45_22_check : sumFast (c3TensorGroup45.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian45_22 := by kernel_rfl
private def c3GroupHessian45_23Chunk0 : Poly := [([0,0], -48),([0,3], -40),([0,4], -4),([0,5], -8),([0,6], -40),([0,7], -40),([0,8], -20),([0,9], 8),([3,6], -40),([4,5], -4),([4,9], -4),([5,8], -20),([5,9], 16),([6,7], -40),([8,9], -20),([9,9], 16)]
def c3GroupHessian45_23 : Poly := List.flatten [c3GroupHessian45_23Chunk0]
theorem c3GroupHessian45_23_check : sumFast (c3TensorGroup45.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian45_23 := by kernel_rfl
private def c3GroupHessian45_33Chunk0 : Poly := [([0,0], 56),([0,4], 8),([0,6], 80),([0,8], 40),([0,9], -16),([4,4], 8),([4,9], -8),([6,6], 40),([8,8], 40),([8,9], -40),([9,9], 16)]
def c3GroupHessian45_33 : Poly := List.flatten [c3GroupHessian45_33Chunk0]
theorem c3GroupHessian45_33_check : sumFast (c3TensorGroup45.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian45_33 := by kernel_rfl
end D4.Secondary
