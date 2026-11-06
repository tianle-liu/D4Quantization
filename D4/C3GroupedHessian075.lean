import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup75_det_check : c3TensorGroup75.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 102)) = true := by kernel_rfl
private def c3GroupHessian75_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 80),([0,6], 8),([0,9], 16),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 16),([6,9], 8),([9,9], 8)]
def c3GroupHessian75_00 : Poly := List.flatten [c3GroupHessian75_00Chunk0]
theorem c3GroupHessian75_00_check : sumFast (c3TensorGroup75.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian75_00 := by kernel_rfl
private def c3GroupHessian75_01Chunk0 : Poly := [([0,0], 12),([0,2], 4),([0,6], -4),([0,7], 8),([0,8], -40),([0,9], 20),([1,8], -40),([2,6], -8),([2,9], 4),([5,8], -40),([6,7], 4),([6,9], 4),([7,9], 8),([9,9], 8)]
def c3GroupHessian75_01 : Poly := List.flatten [c3GroupHessian75_01Chunk0]
theorem c3GroupHessian75_01_check : sumFast (c3TensorGroup75.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian75_01 := by kernel_rfl
private def c3GroupHessian75_02Chunk0 : Poly := [([0,0], -48),([0,1], -40),([0,3], 4),([0,5], -80),([0,6], -4),([0,7], -8),([0,9], -16),([1,5], -40),([3,6], -8),([3,9], 4),([5,5], -40),([6,7], -4),([6,9], -4),([7,9], -8),([9,9], -8)]
def c3GroupHessian75_02 : Poly := List.flatten [c3GroupHessian75_02Chunk0]
theorem c3GroupHessian75_02_check : sumFast (c3TensorGroup75.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian75_02 := by kernel_rfl
private def c3GroupHessian75_03Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -8),([0,8], 40),([0,9], -16),([1,4], 40),([1,8], 40),([4,5], 40),([5,8], 40),([6,6], -16),([6,9], -8),([9,9], -8)]
def c3GroupHessian75_03 : Poly := List.flatten [c3GroupHessian75_03Chunk0]
theorem c3GroupHessian75_03_check : sumFast (c3TensorGroup75.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian75_03 := by kernel_rfl
private def c3GroupHessian75_11Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,7], 24),([0,9], 24),([2,2], 16),([2,7], 8),([2,9], 8),([7,7], 8),([7,9], 16),([8,8], 40),([9,9], 8)]
def c3GroupHessian75_11 : Poly := List.flatten [c3GroupHessian75_11Chunk0]
theorem c3GroupHessian75_11_check : sumFast (c3TensorGroup75.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian75_11 := by kernel_rfl
private def c3GroupHessian75_12Chunk0 : Poly := [([0,0], -12),([0,2], -4),([0,3], 20),([0,7], -20),([0,8], 40),([0,9], -20),([2,3], 16),([2,7], -4),([2,9], -4),([3,7], 4),([3,9], 4),([5,8], 40),([7,7], -8),([7,9], -16),([9,9], -8)]
def c3GroupHessian75_12 : Poly := List.flatten [c3GroupHessian75_12Chunk0]
theorem c3GroupHessian75_12_check : sumFast (c3TensorGroup75.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian75_12 := by kernel_rfl
private def c3GroupHessian75_13Chunk0 : Poly := [([0,0], -12),([0,2], -4),([0,6], 4),([0,7], -8),([0,8], -40),([0,9], -20),([2,6], 8),([2,9], -4),([4,8], -40),([6,7], -4),([6,9], -4),([7,9], -8),([8,8], -40),([9,9], -8)]
def c3GroupHessian75_13 : Poly := List.flatten [c3GroupHessian75_13Chunk0]
theorem c3GroupHessian75_13_check : sumFast (c3TensorGroup75.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian75_13 := by kernel_rfl
private def c3GroupHessian75_22Chunk0 : Poly := [([0,0], 48),([0,3], -8),([0,5], 80),([0,7], 16),([0,9], 16),([3,3], 16),([3,7], -8),([3,9], -8),([5,5], 40),([7,7], 8),([7,9], 16),([9,9], 8)]
def c3GroupHessian75_22 : Poly := List.flatten [c3GroupHessian75_22Chunk0]
theorem c3GroupHessian75_22_check : sumFast (c3TensorGroup75.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian75_22 := by kernel_rfl
private def c3GroupHessian75_23Chunk0 : Poly := [([0,0], -32),([0,3], -4),([0,4], -40),([0,5], -40),([0,6], 4),([0,7], 8),([0,8], -40),([0,9], 16),([3,6], 8),([3,9], -4),([4,5], -40),([5,8], -40),([6,7], 4),([6,9], 4),([7,9], 8),([9,9], 8)]
def c3GroupHessian75_23 : Poly := List.flatten [c3GroupHessian75_23Chunk0]
theorem c3GroupHessian75_23_check : sumFast (c3TensorGroup75.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian75_23 := by kernel_rfl
private def c3GroupHessian75_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 8),([0,8], 80),([0,9], 16),([4,4], 40),([4,8], 80),([6,6], 16),([6,9], 8),([8,8], 40),([9,9], 8)]
def c3GroupHessian75_33 : Poly := List.flatten [c3GroupHessian75_33Chunk0]
theorem c3GroupHessian75_33_check : sumFast (c3TensorGroup75.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian75_33 := by kernel_rfl
end D4.Secondary
