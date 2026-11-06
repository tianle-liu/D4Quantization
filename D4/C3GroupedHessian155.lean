import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup155_det_check : c3TensorGroup155.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 202)) = true := by kernel_rfl
private def c3GroupHessian155_00Chunk0 : Poly := [([0,0], 16),([0,1], -8),([0,5], 40),([0,9], 24),([1,1], 16),([1,5], -40),([1,9], -16),([5,5], 40),([5,9], 40),([6,6], 40),([9,9], 16)]
def c3GroupHessian155_00 : Poly := List.flatten [c3GroupHessian155_00Chunk0]
theorem c3GroupHessian155_00_check : sumFast (c3TensorGroup155.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian155_00 := by kernel_rfl
private def c3GroupHessian155_01Chunk0 : Poly := [([0,0], 4),([0,1], 4),([0,6], -40),([0,8], 4),([0,9], 16),([1,8], 4),([1,9], -8),([2,6], -40),([5,9], 20),([6,7], -40),([8,9], 4),([9,9], 16)]
def c3GroupHessian155_01 : Poly := List.flatten [c3GroupHessian155_01Chunk0]
theorem c3GroupHessian155_01_check : sumFast (c3TensorGroup155.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian155_01 := by kernel_rfl
private def c3GroupHessian155_02Chunk0 : Poly := [([0,0], -20),([0,1], 20),([0,3], -4),([0,5], -60),([0,6], 40),([0,9], -32),([1,3], 16),([1,5], 20),([1,9], 8),([3,5], -20),([3,9], -8),([5,5], -40),([5,9], -40),([6,7], 40),([9,9], -16)]
def c3GroupHessian155_02 : Poly := List.flatten [c3GroupHessian155_02Chunk0]
theorem c3GroupHessian155_02_check : sumFast (c3TensorGroup155.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian155_02 := by kernel_rfl
private def c3GroupHessian155_03Chunk0 : Poly := [([0,0], -4),([0,1], -4),([0,6], -40),([0,8], -4),([0,9], -16),([1,8], -4),([1,9], 8),([4,6], -40),([5,9], -20),([6,6], -40),([8,9], -4),([9,9], -16)]
def c3GroupHessian155_03 : Poly := List.flatten [c3GroupHessian155_03Chunk0]
theorem c3GroupHessian155_03_check : sumFast (c3TensorGroup155.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian155_03 := by kernel_rfl
private def c3GroupHessian155_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 80),([0,8], 16),([0,9], 8),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 8),([8,9], 8),([9,9], 16)]
def c3GroupHessian155_11 : Poly := List.flatten [c3GroupHessian155_11Chunk0]
theorem c3GroupHessian155_11_check : sumFast (c3TensorGroup155.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian155_11 := by kernel_rfl
private def c3GroupHessian155_12Chunk0 : Poly := [([0,0], -40),([0,2], -40),([0,3], 4),([0,7], -80),([0,9], -24),([2,7], -40),([3,8], 4),([3,9], -8),([5,9], -20),([7,7], -40),([8,9], -4),([9,9], -16)]
def c3GroupHessian155_12 : Poly := List.flatten [c3GroupHessian155_12Chunk0]
theorem c3GroupHessian155_12_check : sumFast (c3TensorGroup155.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian155_12 := by kernel_rfl
private def c3GroupHessian155_13Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -16),([0,9], -8),([2,4], 40),([2,6], 40),([4,7], 40),([6,7], 40),([8,8], -8),([8,9], -8),([9,9], -16)]
def c3GroupHessian155_13 : Poly := List.flatten [c3GroupHessian155_13Chunk0]
theorem c3GroupHessian155_13_check : sumFast (c3TensorGroup155.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian155_13 := by kernel_rfl
private def c3GroupHessian155_22Chunk0 : Poly := [([0,0], 80),([0,3], 40),([0,5], 80),([0,7], 80),([0,9], 40),([3,3], 16),([3,5], 40),([3,9], 16),([5,5], 40),([5,9], 40),([7,7], 40),([9,9], 16)]
def c3GroupHessian155_22 : Poly := List.flatten [c3GroupHessian155_22Chunk0]
theorem c3GroupHessian155_22_check : sumFast (c3TensorGroup155.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian155_22 := by kernel_rfl
private def c3GroupHessian155_23Chunk0 : Poly := [([0,0], -40),([0,3], -4),([0,4], -40),([0,6], -40),([0,7], -40),([0,9], 24),([3,8], -4),([3,9], 8),([4,7], -40),([5,9], 20),([6,7], -40),([8,9], 4),([9,9], 16)]
def c3GroupHessian155_23 : Poly := List.flatten [c3GroupHessian155_23Chunk0]
theorem c3GroupHessian155_23_check : sumFast (c3TensorGroup155.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian155_23 := by kernel_rfl
private def c3GroupHessian155_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 80),([0,8], 16),([0,9], 8),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 8),([8,9], 8),([9,9], 16)]
def c3GroupHessian155_33 : Poly := List.flatten [c3GroupHessian155_33Chunk0]
theorem c3GroupHessian155_33_check : sumFast (c3TensorGroup155.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian155_33 := by kernel_rfl
end D4.Secondary
