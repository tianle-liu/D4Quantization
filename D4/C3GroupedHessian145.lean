import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup145_det_check : c3TensorGroup145.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 188)) = true := by kernel_rfl
private def c3GroupHessian145_00Chunk0 : Poly := [([0,0], 16),([0,1], 24),([0,5], 40),([0,9], -8),([1,1], 16),([1,5], 40),([1,9], -16),([5,5], 40),([5,9], -40),([6,6], 40),([9,9], 16)]
def c3GroupHessian145_00 : Poly := List.flatten [c3GroupHessian145_00Chunk0]
theorem c3GroupHessian145_00_check : sumFast (c3TensorGroup145.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian145_00 := by kernel_rfl
private def c3GroupHessian145_01Chunk0 : Poly := [([0,0], -4),([0,1], -8),([0,5], -20),([0,6], -40),([0,8], -4),([0,9], 12),([1,8], -8),([1,9], -8),([2,6], -40),([5,8], -20),([5,9], -20),([6,7], -40),([8,9], 16),([9,9], 16)]
def c3GroupHessian145_01 : Poly := List.flatten [c3GroupHessian145_01Chunk0]
theorem c3GroupHessian145_01_check : sumFast (c3TensorGroup145.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian145_01 := by kernel_rfl
private def c3GroupHessian145_02Chunk0 : Poly := [([0,0], -12),([0,1], -8),([0,3], 4),([0,5], -40),([0,6], 40),([0,9], 12),([1,3], 4),([1,5], -20),([1,9], 8),([3,9], 4),([5,5], -40),([5,9], 40),([6,7], 40),([9,9], -16)]
def c3GroupHessian145_02 : Poly := List.flatten [c3GroupHessian145_02Chunk0]
theorem c3GroupHessian145_02_check : sumFast (c3TensorGroup145.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian145_02 := by kernel_rfl
private def c3GroupHessian145_03Chunk0 : Poly := [([0,0], 4),([0,1], 8),([0,5], 20),([0,6], -40),([0,8], 4),([0,9], -12),([1,8], 8),([1,9], 8),([4,6], -40),([5,8], 20),([5,9], 20),([6,6], -40),([8,9], -16),([9,9], -16)]
def c3GroupHessian145_03 : Poly := List.flatten [c3GroupHessian145_03Chunk0]
theorem c3GroupHessian145_03_check : sumFast (c3TensorGroup145.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian145_03 := by kernel_rfl
private def c3GroupHessian145_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 80),([0,8], 32),([0,9], 32),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 16),([8,9], 32),([9,9], 16)]
def c3GroupHessian145_11 : Poly := List.flatten [c3GroupHessian145_11Chunk0]
theorem c3GroupHessian145_11_check : sumFast (c3TensorGroup145.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian145_11 := by kernel_rfl
private def c3GroupHessian145_12Chunk0 : Poly := [([0,0], -32),([0,2], -40),([0,3], 4),([0,5], 20),([0,7], -80),([0,8], 8),([0,9], -8),([2,7], -40),([3,8], 4),([3,9], 4),([5,8], 20),([5,9], 20),([7,7], -40),([8,9], -16),([9,9], -16)]
def c3GroupHessian145_12 : Poly := List.flatten [c3GroupHessian145_12Chunk0]
theorem c3GroupHessian145_12_check : sumFast (c3TensorGroup145.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian145_12 := by kernel_rfl
private def c3GroupHessian145_13Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -32),([0,9], -32),([2,4], 40),([2,6], 40),([4,7], 40),([6,7], 40),([8,8], -16),([8,9], -32),([9,9], -16)]
def c3GroupHessian145_13 : Poly := List.flatten [c3GroupHessian145_13Chunk0]
theorem c3GroupHessian145_13_check : sumFast (c3TensorGroup145.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian145_13 := by kernel_rfl
private def c3GroupHessian145_22Chunk0 : Poly := [([0,0], 56),([0,3], 8),([0,5], 40),([0,7], 80),([0,9], -16),([3,3], 8),([3,9], -8),([5,5], 40),([5,9], -40),([7,7], 40),([9,9], 16)]
def c3GroupHessian145_22 : Poly := List.flatten [c3GroupHessian145_22Chunk0]
theorem c3GroupHessian145_22_check : sumFast (c3TensorGroup145.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian145_22 := by kernel_rfl
private def c3GroupHessian145_23Chunk0 : Poly := [([0,0], -48),([0,3], -4),([0,4], -40),([0,5], -20),([0,6], -40),([0,7], -40),([0,8], -8),([0,9], 8),([3,8], -4),([3,9], -4),([4,7], -40),([5,8], -20),([5,9], -20),([6,7], -40),([8,9], 16),([9,9], 16)]
def c3GroupHessian145_23 : Poly := List.flatten [c3GroupHessian145_23Chunk0]
theorem c3GroupHessian145_23_check : sumFast (c3TensorGroup145.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian145_23 := by kernel_rfl
private def c3GroupHessian145_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 80),([0,8], 32),([0,9], 32),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 16),([8,9], 32),([9,9], 16)]
def c3GroupHessian145_33 : Poly := List.flatten [c3GroupHessian145_33Chunk0]
theorem c3GroupHessian145_33_check : sumFast (c3TensorGroup145.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian145_33 := by kernel_rfl
end D4.Secondary
