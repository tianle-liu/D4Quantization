import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup12_det_check : c3TensorGroup12.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 13)) = true := by kernel_rfl
private def c3GroupHessian12_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 32),([0,6], 32),([0,9], 32),([1,1], 40),([5,5], 16),([5,6], 32),([5,9], 32),([6,6], 16),([6,9], 32),([9,9], 16)]
def c3GroupHessian12_00 : Poly := List.flatten [c3GroupHessian12_00Chunk0]
theorem c3GroupHessian12_00_check : sumFast (c3TensorGroup12.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian12_00 := by kernel_rfl
private def c3GroupHessian12_01Chunk0 : Poly := [([0,0], 44),([0,1], 40),([0,2], 40),([0,5], 4),([0,6], 4),([0,7], 4),([0,8], 4),([0,9], 20),([1,2], 40),([5,7], 4),([5,8], 4),([5,9], 16),([6,7], 4),([6,8], 4),([6,9], 16),([7,9], 4),([8,9], 4),([9,9], 16)]
def c3GroupHessian12_01 : Poly := List.flatten [c3GroupHessian12_01Chunk0]
theorem c3GroupHessian12_01_check : sumFast (c3TensorGroup12.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian12_01 := by kernel_rfl
private def c3GroupHessian12_02Chunk0 : Poly := [([0,0], -12),([0,3], 40),([0,5], -28),([0,6], -12),([0,7], -4),([0,9], -28),([1,3], 40),([5,5], -16),([5,6], -16),([5,7], -4),([5,9], -32),([6,7], -4),([6,9], -16),([7,9], -4),([9,9], -16)]
def c3GroupHessian12_02 : Poly := List.flatten [c3GroupHessian12_02Chunk0]
theorem c3GroupHessian12_02_check : sumFast (c3TensorGroup12.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian12_02 := by kernel_rfl
private def c3GroupHessian12_03Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,5], -8),([0,6], -24),([0,8], -4),([0,9], -24),([1,4], 40),([5,6], -16),([5,8], -4),([5,9], -16),([6,6], -16),([6,8], -4),([6,9], -32),([8,9], -4),([9,9], -16)]
def c3GroupHessian12_03 : Poly := List.flatten [c3GroupHessian12_03Chunk0]
theorem c3GroupHessian12_03_check : sumFast (c3TensorGroup12.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian12_03 := by kernel_rfl
private def c3GroupHessian12_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 16),([0,8], 16),([0,9], 8),([2,2], 40),([7,7], 8),([7,8], 16),([7,9], 8),([8,8], 8),([8,9], 8),([9,9], 16)]
def c3GroupHessian12_11 : Poly := List.flatten [c3GroupHessian12_11Chunk0]
theorem c3GroupHessian12_11_check : sumFast (c3TensorGroup12.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian12_11 := by kernel_rfl
private def c3GroupHessian12_12Chunk0 : Poly := [([0,0], -4),([0,3], 40),([0,5], -4),([0,7], -12),([0,8], -4),([0,9], -16),([2,3], 40),([5,7], -4),([5,8], -4),([5,9], -16),([7,7], -8),([7,8], -8),([7,9], -8),([8,9], -4),([9,9], -16)]
def c3GroupHessian12_12 : Poly := List.flatten [c3GroupHessian12_12Chunk0]
theorem c3GroupHessian12_12_check : sumFast (c3TensorGroup12.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian12_12 := by kernel_rfl
private def c3GroupHessian12_13Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,6], -4),([0,7], -8),([0,8], -16),([0,9], -12),([2,4], 40),([6,7], -4),([6,8], -4),([6,9], -16),([7,8], -8),([7,9], -4),([8,8], -8),([8,9], -8),([9,9], -16)]
def c3GroupHessian12_13 : Poly := List.flatten [c3GroupHessian12_13Chunk0]
theorem c3GroupHessian12_13_check : sumFast (c3TensorGroup12.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian12_13 := by kernel_rfl
private def c3GroupHessian12_22Chunk0 : Poly := [([0,0], 16),([0,5], 24),([0,7], 8),([0,9], 24),([3,3], 40),([5,5], 16),([5,7], 8),([5,9], 32),([7,7], 8),([7,9], 8),([9,9], 16)]
def c3GroupHessian12_22 : Poly := List.flatten [c3GroupHessian12_22Chunk0]
theorem c3GroupHessian12_22_check : sumFast (c3TensorGroup12.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian12_22 := by kernel_rfl
private def c3GroupHessian12_23Chunk0 : Poly := [([0,5], 8),([0,6], 12),([0,7], 8),([0,8], 4),([0,9], 20),([3,4], 40),([5,6], 16),([5,8], 4),([5,9], 16),([6,7], 4),([6,9], 16),([7,8], 8),([7,9], 4),([8,9], 4),([9,9], 16)]
def c3GroupHessian12_23 : Poly := List.flatten [c3GroupHessian12_23Chunk0]
theorem c3GroupHessian12_23_check : sumFast (c3TensorGroup12.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian12_23 := by kernel_rfl
private def c3GroupHessian12_33Chunk0 : Poly := [([0,0], 16),([0,6], 16),([0,8], 16),([0,9], 16),([4,4], 40),([6,6], 16),([6,8], 8),([6,9], 32),([8,8], 8),([8,9], 8),([9,9], 16)]
def c3GroupHessian12_33 : Poly := List.flatten [c3GroupHessian12_33Chunk0]
theorem c3GroupHessian12_33_check : sumFast (c3TensorGroup12.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian12_33 := by kernel_rfl
end D4.Secondary
