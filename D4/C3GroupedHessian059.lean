import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup59_det_check : c3TensorGroup59.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 82)) = true := by kernel_rfl
private def c3GroupHessian59_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 80),([0,6], 40),([0,9], 8),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 40),([9,9], 8)]
def c3GroupHessian59_00 : Poly := List.flatten [c3GroupHessian59_00Chunk0]
theorem c3GroupHessian59_00_check : sumFast (c3TensorGroup59.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian59_00 := by kernel_rfl
private def c3GroupHessian59_01Chunk0 : Poly := [([0,0], 8),([0,2], -8),([0,7], -8),([0,8], -40),([0,9], 12),([1,8], -40),([2,6], -20),([2,9], 4),([5,8], -40),([6,7], -20),([7,9], 4),([9,9], 8)]
def c3GroupHessian59_01 : Poly := List.flatten [c3GroupHessian59_01Chunk0]
theorem c3GroupHessian59_01_check : sumFast (c3TensorGroup59.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian59_01 := by kernel_rfl
private def c3GroupHessian59_02Chunk0 : Poly := [([0,0], -32),([0,1], -40),([0,3], 20),([0,5], -80),([0,6], 20),([0,7], 8),([0,9], -8),([1,5], -40),([3,6], 40),([5,5], -40),([6,7], 20),([7,9], -4),([9,9], -8)]
def c3GroupHessian59_02 : Poly := List.flatten [c3GroupHessian59_02Chunk0]
theorem c3GroupHessian59_02_check : sumFast (c3TensorGroup59.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian59_02 := by kernel_rfl
private def c3GroupHessian59_03Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -40),([0,8], 40),([0,9], -8),([1,4], 40),([1,8], 40),([4,5], 40),([5,8], 40),([6,6], -40),([9,9], -8)]
def c3GroupHessian59_03 : Poly := List.flatten [c3GroupHessian59_03Chunk0]
theorem c3GroupHessian59_03_check : sumFast (c3TensorGroup59.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian59_03 := by kernel_rfl
private def c3GroupHessian59_11Chunk0 : Poly := [([0,0], 16),([0,2], 16),([0,7], 16),([0,9], 16),([2,2], 16),([2,7], 32),([2,9], 8),([7,7], 16),([7,9], 8),([8,8], 40),([9,9], 8)]
def c3GroupHessian59_11 : Poly := List.flatten [c3GroupHessian59_11Chunk0]
theorem c3GroupHessian59_11_check : sumFast (c3TensorGroup59.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian59_11 := by kernel_rfl
private def c3GroupHessian59_12Chunk0 : Poly := [([0,0], -8),([0,2], -16),([0,7], -24),([0,8], 40),([0,9], -12),([2,3], -20),([2,7], -16),([2,9], -4),([3,7], -20),([5,8], 40),([7,7], -16),([7,9], -8),([9,9], -8)]
def c3GroupHessian59_12 : Poly := List.flatten [c3GroupHessian59_12Chunk0]
theorem c3GroupHessian59_12_check : sumFast (c3TensorGroup59.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian59_12 := by kernel_rfl
private def c3GroupHessian59_13Chunk0 : Poly := [([0,0], -8),([0,2], 8),([0,7], 8),([0,8], -40),([0,9], -12),([2,6], 20),([2,9], -4),([4,8], -40),([6,7], 20),([7,9], -4),([8,8], -40),([9,9], -8)]
def c3GroupHessian59_13 : Poly := List.flatten [c3GroupHessian59_13Chunk0]
theorem c3GroupHessian59_13_check : sumFast (c3TensorGroup59.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian59_13 := by kernel_rfl
private def c3GroupHessian59_22Chunk0 : Poly := [([0,0], 56),([0,3], 40),([0,5], 80),([0,7], 32),([0,9], 8),([3,3], 40),([3,7], 40),([5,5], 40),([7,7], 16),([7,9], 8),([9,9], 8)]
def c3GroupHessian59_22 : Poly := List.flatten [c3GroupHessian59_22Chunk0]
theorem c3GroupHessian59_22_check : sumFast (c3TensorGroup59.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian59_22 := by kernel_rfl
private def c3GroupHessian59_23Chunk0 : Poly := [([0,0], -48),([0,3], -20),([0,4], -40),([0,5], -40),([0,6], -20),([0,7], -8),([0,8], -40),([0,9], 8),([3,6], -40),([4,5], -40),([5,8], -40),([6,7], -20),([7,9], 4),([9,9], 8)]
def c3GroupHessian59_23 : Poly := List.flatten [c3GroupHessian59_23Chunk0]
theorem c3GroupHessian59_23_check : sumFast (c3TensorGroup59.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian59_23 := by kernel_rfl
private def c3GroupHessian59_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 40),([0,8], 80),([0,9], 8),([4,4], 40),([4,8], 80),([6,6], 40),([8,8], 40),([9,9], 8)]
def c3GroupHessian59_33 : Poly := List.flatten [c3GroupHessian59_33Chunk0]
theorem c3GroupHessian59_33_check : sumFast (c3TensorGroup59.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian59_33 := by kernel_rfl
end D4.Secondary
