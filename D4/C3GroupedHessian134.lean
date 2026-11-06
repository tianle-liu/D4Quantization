import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup134_det_check : c3TensorGroup134.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 176)) = true := by kernel_rfl
private def c3GroupHessian134_00Chunk0 : Poly := [([0,0], 16),([0,1], -8),([0,6], 40),([0,9], 24),([1,1], 16),([1,6], -40),([1,9], -16),([5,5], 40),([6,6], 40),([6,9], 40),([9,9], 16)]
def c3GroupHessian134_00 : Poly := List.flatten [c3GroupHessian134_00Chunk0]
theorem c3GroupHessian134_00_check : sumFast (c3TensorGroup134.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian134_00 := by kernel_rfl
private def c3GroupHessian134_01Chunk0 : Poly := [([0,0], 4),([0,1], 4),([0,5], -40),([0,7], 4),([0,9], 16),([1,7], 4),([1,9], -8),([2,5], -40),([5,8], -40),([6,9], 20),([7,9], 4),([9,9], 16)]
def c3GroupHessian134_01 : Poly := List.flatten [c3GroupHessian134_01Chunk0]
theorem c3GroupHessian134_01_check : sumFast (c3TensorGroup134.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian134_01 := by kernel_rfl
private def c3GroupHessian134_02Chunk0 : Poly := [([0,0], -4),([0,1], -4),([0,5], -40),([0,7], -4),([0,9], -16),([1,7], -4),([1,9], 8),([3,5], -40),([5,5], -40),([6,9], -20),([7,9], -4),([9,9], -16)]
def c3GroupHessian134_02 : Poly := List.flatten [c3GroupHessian134_02Chunk0]
theorem c3GroupHessian134_02_check : sumFast (c3TensorGroup134.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian134_02 := by kernel_rfl
private def c3GroupHessian134_03Chunk0 : Poly := [([0,0], -20),([0,1], 20),([0,4], -4),([0,5], 40),([0,6], -60),([0,9], -32),([1,4], 16),([1,6], 20),([1,9], 8),([4,6], -20),([4,9], -8),([5,8], 40),([6,6], -40),([6,9], -40),([9,9], -16)]
def c3GroupHessian134_03 : Poly := List.flatten [c3GroupHessian134_03Chunk0]
theorem c3GroupHessian134_03_check : sumFast (c3TensorGroup134.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian134_03 := by kernel_rfl
private def c3GroupHessian134_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 16),([0,8], 80),([0,9], 8),([2,2], 40),([2,8], 80),([7,7], 8),([7,9], 8),([8,8], 40),([9,9], 16)]
def c3GroupHessian134_11 : Poly := List.flatten [c3GroupHessian134_11Chunk0]
theorem c3GroupHessian134_11_check : sumFast (c3TensorGroup134.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian134_11 := by kernel_rfl
private def c3GroupHessian134_12Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -16),([0,8], 40),([0,9], -8),([2,3], 40),([2,5], 40),([3,8], 40),([5,8], 40),([7,7], -8),([7,9], -8),([9,9], -16)]
def c3GroupHessian134_12 : Poly := List.flatten [c3GroupHessian134_12Chunk0]
theorem c3GroupHessian134_12_check : sumFast (c3TensorGroup134.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian134_12 := by kernel_rfl
private def c3GroupHessian134_13Chunk0 : Poly := [([0,0], -40),([0,2], -40),([0,4], 4),([0,8], -80),([0,9], -24),([2,8], -40),([4,7], 4),([4,9], -8),([6,9], -20),([7,9], -4),([8,8], -40),([9,9], -16)]
def c3GroupHessian134_13 : Poly := List.flatten [c3GroupHessian134_13Chunk0]
theorem c3GroupHessian134_13_check : sumFast (c3TensorGroup134.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian134_13 := by kernel_rfl
private def c3GroupHessian134_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 80),([0,7], 16),([0,9], 8),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 8),([7,9], 8),([9,9], 16)]
def c3GroupHessian134_22 : Poly := List.flatten [c3GroupHessian134_22Chunk0]
theorem c3GroupHessian134_22_check : sumFast (c3TensorGroup134.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian134_22 := by kernel_rfl
private def c3GroupHessian134_23Chunk0 : Poly := [([0,0], -40),([0,3], -40),([0,4], -4),([0,5], -40),([0,8], -40),([0,9], 24),([3,8], -40),([4,7], -4),([4,9], 8),([5,8], -40),([6,9], 20),([7,9], 4),([9,9], 16)]
def c3GroupHessian134_23 : Poly := List.flatten [c3GroupHessian134_23Chunk0]
theorem c3GroupHessian134_23_check : sumFast (c3TensorGroup134.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian134_23 := by kernel_rfl
private def c3GroupHessian134_33Chunk0 : Poly := [([0,0], 80),([0,4], 40),([0,6], 80),([0,8], 80),([0,9], 40),([4,4], 16),([4,6], 40),([4,9], 16),([6,6], 40),([6,9], 40),([8,8], 40),([9,9], 16)]
def c3GroupHessian134_33 : Poly := List.flatten [c3GroupHessian134_33Chunk0]
theorem c3GroupHessian134_33_check : sumFast (c3TensorGroup134.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian134_33 := by kernel_rfl
end D4.Secondary
