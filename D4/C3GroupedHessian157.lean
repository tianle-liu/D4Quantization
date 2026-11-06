import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup157_det_check : c3TensorGroup157.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 204)) = true := by kernel_rfl
private def c3GroupHessian157_00Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,5], 24),([0,9], 24),([1,1], 16),([1,5], 8),([1,9], 8),([5,5], 8),([5,9], 16),([6,6], 40),([9,9], 8)]
def c3GroupHessian157_00 : Poly := List.flatten [c3GroupHessian157_00Chunk0]
theorem c3GroupHessian157_00_check : sumFast (c3TensorGroup157.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian157_00 := by kernel_rfl
private def c3GroupHessian157_01Chunk0 : Poly := [([0,0], 12),([0,1], 4),([0,5], 8),([0,6], -40),([0,8], -4),([0,9], 20),([1,8], -8),([1,9], 4),([2,6], -40),([5,8], 4),([5,9], 8),([6,7], -40),([8,9], 4),([9,9], 8)]
def c3GroupHessian157_01 : Poly := List.flatten [c3GroupHessian157_01Chunk0]
theorem c3GroupHessian157_01_check : sumFast (c3TensorGroup157.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian157_01 := by kernel_rfl
private def c3GroupHessian157_02Chunk0 : Poly := [([0,0], -12),([0,1], -4),([0,3], 20),([0,5], -20),([0,6], 40),([0,9], -20),([1,3], 16),([1,5], -4),([1,9], -4),([3,5], 4),([3,9], 4),([5,5], -8),([5,9], -16),([6,7], 40),([9,9], -8)]
def c3GroupHessian157_02 : Poly := List.flatten [c3GroupHessian157_02Chunk0]
theorem c3GroupHessian157_02_check : sumFast (c3TensorGroup157.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian157_02 := by kernel_rfl
private def c3GroupHessian157_03Chunk0 : Poly := [([0,0], -12),([0,1], -4),([0,5], -8),([0,6], -40),([0,8], 4),([0,9], -20),([1,8], 8),([1,9], -4),([4,6], -40),([5,8], -4),([5,9], -8),([6,6], -40),([8,9], -4),([9,9], -8)]
def c3GroupHessian157_03 : Poly := List.flatten [c3GroupHessian157_03Chunk0]
theorem c3GroupHessian157_03_check : sumFast (c3TensorGroup157.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian157_03 := by kernel_rfl
private def c3GroupHessian157_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 80),([0,8], 8),([0,9], 16),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 16),([8,9], 8),([9,9], 8)]
def c3GroupHessian157_11 : Poly := List.flatten [c3GroupHessian157_11Chunk0]
theorem c3GroupHessian157_11_check : sumFast (c3TensorGroup157.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian157_11 := by kernel_rfl
private def c3GroupHessian157_12Chunk0 : Poly := [([0,0], -48),([0,2], -40),([0,3], 4),([0,5], -8),([0,7], -80),([0,8], -4),([0,9], -16),([2,7], -40),([3,8], -8),([3,9], 4),([5,8], -4),([5,9], -8),([7,7], -40),([8,9], -4),([9,9], -8)]
def c3GroupHessian157_12 : Poly := List.flatten [c3GroupHessian157_12Chunk0]
theorem c3GroupHessian157_12_check : sumFast (c3TensorGroup157.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian157_12 := by kernel_rfl
private def c3GroupHessian157_13Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -8),([0,9], -16),([2,4], 40),([2,6], 40),([4,7], 40),([6,7], 40),([8,8], -16),([8,9], -8),([9,9], -8)]
def c3GroupHessian157_13 : Poly := List.flatten [c3GroupHessian157_13Chunk0]
theorem c3GroupHessian157_13_check : sumFast (c3TensorGroup157.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian157_13 := by kernel_rfl
private def c3GroupHessian157_22Chunk0 : Poly := [([0,0], 48),([0,3], -8),([0,5], 16),([0,7], 80),([0,9], 16),([3,3], 16),([3,5], -8),([3,9], -8),([5,5], 8),([5,9], 16),([7,7], 40),([9,9], 8)]
def c3GroupHessian157_22 : Poly := List.flatten [c3GroupHessian157_22Chunk0]
theorem c3GroupHessian157_22_check : sumFast (c3TensorGroup157.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian157_22 := by kernel_rfl
private def c3GroupHessian157_23Chunk0 : Poly := [([0,0], -32),([0,3], -4),([0,4], -40),([0,5], 8),([0,6], -40),([0,7], -40),([0,8], 4),([0,9], 16),([3,8], 8),([3,9], -4),([4,7], -40),([5,8], 4),([5,9], 8),([6,7], -40),([8,9], 4),([9,9], 8)]
def c3GroupHessian157_23 : Poly := List.flatten [c3GroupHessian157_23Chunk0]
theorem c3GroupHessian157_23_check : sumFast (c3TensorGroup157.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian157_23 := by kernel_rfl
private def c3GroupHessian157_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 80),([0,8], 8),([0,9], 16),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 16),([8,9], 8),([9,9], 8)]
def c3GroupHessian157_33 : Poly := List.flatten [c3GroupHessian157_33Chunk0]
theorem c3GroupHessian157_33_check : sumFast (c3TensorGroup157.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian157_33 := by kernel_rfl
end D4.Secondary
