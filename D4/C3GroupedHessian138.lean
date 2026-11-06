import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup138_det_check : c3TensorGroup138.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 180)) = true := by kernel_rfl
private def c3GroupHessian138_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 80),([0,9], 48),([1,1], 40),([1,5], 80),([1,9], 40),([5,5], 40),([5,9], 40),([6,6], 40),([9,9], 16)]
def c3GroupHessian138_00 : Poly := List.flatten [c3GroupHessian138_00Chunk0]
theorem c3GroupHessian138_00_check : sumFast (c3TensorGroup138.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian138_00 := by kernel_rfl
private def c3GroupHessian138_01Chunk0 : Poly := [([0,0], 8),([0,6], -40),([0,8], -16),([0,9], 28),([1,8], -20),([1,9], 20),([2,6], -40),([5,8], -20),([5,9], 20),([6,7], -40),([8,9], -8),([9,9], 16)]
def c3GroupHessian138_01 : Poly := List.flatten [c3GroupHessian138_01Chunk0]
theorem c3GroupHessian138_01_check : sumFast (c3TensorGroup138.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian138_01 := by kernel_rfl
private def c3GroupHessian138_02Chunk0 : Poly := [([0,0], -40),([0,1], -40),([0,3], 8),([0,5], -80),([0,6], 40),([0,9], -44),([1,5], -40),([1,9], -20),([3,9], 4),([5,5], -40),([5,9], -40),([6,7], 40),([9,9], -16)]
def c3GroupHessian138_02 : Poly := List.flatten [c3GroupHessian138_02Chunk0]
theorem c3GroupHessian138_02_check : sumFast (c3TensorGroup138.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian138_02 := by kernel_rfl
private def c3GroupHessian138_03Chunk0 : Poly := [([0,0], -8),([0,6], -40),([0,8], 16),([0,9], -28),([1,8], 20),([1,9], -20),([4,6], -40),([5,8], 20),([5,9], -20),([6,6], -40),([8,9], 8),([9,9], -16)]
def c3GroupHessian138_03 : Poly := List.flatten [c3GroupHessian138_03Chunk0]
theorem c3GroupHessian138_03_check : sumFast (c3TensorGroup138.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian138_03 := by kernel_rfl
private def c3GroupHessian138_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 80),([0,8], 8),([0,9], 8),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 16),([8,9], -16),([9,9], 16)]
def c3GroupHessian138_11 : Poly := List.flatten [c3GroupHessian138_11Chunk0]
theorem c3GroupHessian138_11_check : sumFast (c3TensorGroup138.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian138_11 := by kernel_rfl
private def c3GroupHessian138_12Chunk0 : Poly := [([0,0], -40),([0,2], -40),([0,3], 8),([0,7], -80),([0,8], 20),([0,9], -24),([2,7], -40),([3,8], 4),([3,9], 4),([5,8], 20),([5,9], -20),([7,7], -40),([8,9], 8),([9,9], -16)]
def c3GroupHessian138_12 : Poly := List.flatten [c3GroupHessian138_12Chunk0]
theorem c3GroupHessian138_12_check : sumFast (c3TensorGroup138.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian138_12 := by kernel_rfl
private def c3GroupHessian138_13Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -8),([0,9], -8),([2,4], 40),([2,6], 40),([4,7], 40),([6,7], 40),([8,8], -16),([8,9], 16),([9,9], -16)]
def c3GroupHessian138_13 : Poly := List.flatten [c3GroupHessian138_13Chunk0]
theorem c3GroupHessian138_13_check : sumFast (c3TensorGroup138.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian138_13 := by kernel_rfl
private def c3GroupHessian138_22Chunk0 : Poly := [([0,0], 80),([0,5], 80),([0,7], 80),([0,9], 40),([3,3], 8),([3,9], -8),([5,5], 40),([5,9], 40),([7,7], 40),([9,9], 16)]
def c3GroupHessian138_22 : Poly := List.flatten [c3GroupHessian138_22Chunk0]
theorem c3GroupHessian138_22_check : sumFast (c3TensorGroup138.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian138_22 := by kernel_rfl
private def c3GroupHessian138_23Chunk0 : Poly := [([0,0], -40),([0,3], -8),([0,4], -40),([0,6], -40),([0,7], -40),([0,8], -20),([0,9], 24),([3,8], -4),([3,9], -4),([4,7], -40),([5,8], -20),([5,9], 20),([6,7], -40),([8,9], -8),([9,9], 16)]
def c3GroupHessian138_23 : Poly := List.flatten [c3GroupHessian138_23Chunk0]
theorem c3GroupHessian138_23_check : sumFast (c3TensorGroup138.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian138_23 := by kernel_rfl
private def c3GroupHessian138_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 80),([0,8], 8),([0,9], 8),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 16),([8,9], -16),([9,9], 16)]
def c3GroupHessian138_33 : Poly := List.flatten [c3GroupHessian138_33Chunk0]
theorem c3GroupHessian138_33_check : sumFast (c3TensorGroup138.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian138_33 := by kernel_rfl
end D4.Secondary
