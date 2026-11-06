import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup39_det_check : c3TensorGroup39.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 57)) = true := by kernel_rfl
private def c3GroupHessian39_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,6], 80),([0,9], 16),([1,1], 40),([1,6], 80),([5,5], 40),([6,6], 40),([9,9], 8)]
def c3GroupHessian39_00 : Poly := List.flatten [c3GroupHessian39_00Chunk0]
theorem c3GroupHessian39_00_check : sumFast (c3TensorGroup39.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian39_00 := by kernel_rfl
private def c3GroupHessian39_01Chunk0 : Poly := [([0,0], 12),([0,2], 4),([0,5], -20),([0,7], -40),([0,8], 4),([0,9], 20),([1,7], -40),([2,5], -20),([2,9], 4),([5,8], -20),([6,7], -40),([8,9], 4),([9,9], 8)]
def c3GroupHessian39_01 : Poly := List.flatten [c3GroupHessian39_01Chunk0]
theorem c3GroupHessian39_01_check : sumFast (c3TensorGroup39.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian39_01 := by kernel_rfl
private def c3GroupHessian39_02Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,3], 40),([0,6], 40),([0,7], 40),([0,9], -16),([1,3], 40),([1,7], 40),([3,6], 40),([5,5], -40),([6,7], 40),([9,9], -8)]
def c3GroupHessian39_02 : Poly := List.flatten [c3GroupHessian39_02Chunk0]
theorem c3GroupHessian39_02_check : sumFast (c3TensorGroup39.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian39_02 := by kernel_rfl
private def c3GroupHessian39_03Chunk0 : Poly := [([0,0], -44),([0,1], -40),([0,4], 4),([0,5], 20),([0,6], -80),([0,8], -4),([0,9], -12),([1,6], -40),([4,5], 20),([4,9], 4),([5,8], 20),([6,6], -40),([8,9], -4),([9,9], -8)]
def c3GroupHessian39_03 : Poly := List.flatten [c3GroupHessian39_03Chunk0]
theorem c3GroupHessian39_03_check : sumFast (c3TensorGroup39.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian39_03 := by kernel_rfl
private def c3GroupHessian39_11Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,8], 40),([0,9], 24),([2,2], 16),([2,8], 32),([2,9], 8),([7,7], 40),([8,8], 16),([8,9], 8),([9,9], 8)]
def c3GroupHessian39_11 : Poly := List.flatten [c3GroupHessian39_11Chunk0]
theorem c3GroupHessian39_11_check : sumFast (c3TensorGroup39.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian39_11 := by kernel_rfl
private def c3GroupHessian39_12Chunk0 : Poly := [([0,0], -12),([0,2], -4),([0,5], 20),([0,7], -40),([0,8], -4),([0,9], -20),([2,5], 20),([2,9], -4),([3,7], -40),([5,8], 20),([7,7], -40),([8,9], -4),([9,9], -8)]
def c3GroupHessian39_12 : Poly := List.flatten [c3GroupHessian39_12Chunk0]
theorem c3GroupHessian39_12_check : sumFast (c3TensorGroup39.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian39_12 := by kernel_rfl
private def c3GroupHessian39_13Chunk0 : Poly := [([0,0], -20),([0,2], -16),([0,4], -4),([0,7], 40),([0,8], -36),([0,9], -16),([2,4], -8),([2,8], -16),([2,9], -4),([4,8], -8),([4,9], 4),([6,7], 40),([8,8], -16),([8,9], -8),([9,9], -8)]
def c3GroupHessian39_13 : Poly := List.flatten [c3GroupHessian39_13Chunk0]
theorem c3GroupHessian39_13_check : sumFast (c3TensorGroup39.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian39_13 := by kernel_rfl
private def c3GroupHessian39_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,7], 80),([0,9], 16),([3,3], 40),([3,7], 80),([5,5], 40),([7,7], 40),([9,9], 8)]
def c3GroupHessian39_22 : Poly := List.flatten [c3GroupHessian39_22Chunk0]
theorem c3GroupHessian39_22_check : sumFast (c3TensorGroup39.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian39_22 := by kernel_rfl
private def c3GroupHessian39_23Chunk0 : Poly := [([0,0], -36),([0,3], -40),([0,4], -4),([0,5], -20),([0,6], -40),([0,7], -40),([0,8], 4),([0,9], 12),([3,6], -40),([4,5], -20),([4,9], -4),([5,8], -20),([6,7], -40),([8,9], 4),([9,9], 8)]
def c3GroupHessian39_23 : Poly := List.flatten [c3GroupHessian39_23Chunk0]
theorem c3GroupHessian39_23_check : sumFast (c3TensorGroup39.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian39_23 := by kernel_rfl
private def c3GroupHessian39_33Chunk0 : Poly := [([0,0], 56),([0,4], 16),([0,6], 80),([0,8], 32),([0,9], 8),([4,4], 16),([4,8], 16),([4,9], -8),([6,6], 40),([8,8], 16),([8,9], 8),([9,9], 8)]
def c3GroupHessian39_33 : Poly := List.flatten [c3GroupHessian39_33Chunk0]
theorem c3GroupHessian39_33_check : sumFast (c3TensorGroup39.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian39_33 := by kernel_rfl
end D4.Secondary
