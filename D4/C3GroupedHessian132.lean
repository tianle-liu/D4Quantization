import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup132_det_check : c3TensorGroup132.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 172)) = true := by kernel_rfl
private def c3GroupHessian132_00Chunk0 : Poly := [([0,0], 16),([0,1], 16),([0,6], 16),([0,9], 16),([1,1], 16),([1,6], 32),([1,9], -16),([5,5], 40),([6,6], 16),([6,9], -16),([9,9], 16)]
def c3GroupHessian132_00 : Poly := List.flatten [c3GroupHessian132_00Chunk0]
theorem c3GroupHessian132_00_check : sumFast (c3TensorGroup132.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian132_00 := by kernel_rfl
private def c3GroupHessian132_01Chunk0 : Poly := [([0,0], 8),([0,1], -8),([0,5], -40),([0,6], -8),([0,9], 24),([1,7], -20),([1,9], -8),([2,5], -40),([5,8], -40),([6,7], -20),([6,9], -8),([7,9], 20),([9,9], 16)]
def c3GroupHessian132_01 : Poly := List.flatten [c3GroupHessian132_01Chunk0]
theorem c3GroupHessian132_01_check : sumFast (c3TensorGroup132.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian132_01 := by kernel_rfl
private def c3GroupHessian132_02Chunk0 : Poly := [([0,0], -8),([0,1], 8),([0,5], -40),([0,6], 8),([0,9], -24),([1,7], 20),([1,9], 8),([3,5], -40),([5,5], -40),([6,7], 20),([6,9], 8),([7,9], -20),([9,9], -16)]
def c3GroupHessian132_02 : Poly := List.flatten [c3GroupHessian132_02Chunk0]
theorem c3GroupHessian132_02_check : sumFast (c3TensorGroup132.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian132_02 := by kernel_rfl
private def c3GroupHessian132_03Chunk0 : Poly := [([0,0], -8),([0,1], -4),([0,4], 8),([0,5], 40),([0,6], -12),([0,9], -12),([1,4], 4),([1,6], -16),([1,9], 8),([4,6], 4),([4,9], 4),([5,8], 40),([6,6], -16),([6,9], 16),([9,9], -16)]
def c3GroupHessian132_03 : Poly := List.flatten [c3GroupHessian132_03Chunk0]
theorem c3GroupHessian132_03_check : sumFast (c3TensorGroup132.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian132_03 := by kernel_rfl
private def c3GroupHessian132_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 40),([0,8], 80),([0,9], 32),([2,2], 40),([2,8], 80),([7,7], 40),([7,9], 40),([8,8], 40),([9,9], 16)]
def c3GroupHessian132_11 : Poly := List.flatten [c3GroupHessian132_11Chunk0]
theorem c3GroupHessian132_11_check : sumFast (c3TensorGroup132.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian132_11 := by kernel_rfl
private def c3GroupHessian132_12Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -40),([0,8], 40),([0,9], -32),([2,3], 40),([2,5], 40),([3,8], 40),([5,8], 40),([7,7], -40),([7,9], -40),([9,9], -16)]
def c3GroupHessian132_12 : Poly := List.flatten [c3GroupHessian132_12Chunk0]
theorem c3GroupHessian132_12_check : sumFast (c3TensorGroup132.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian132_12 := by kernel_rfl
private def c3GroupHessian132_13Chunk0 : Poly := [([0,0], -44),([0,2], -40),([0,4], 4),([0,6], 8),([0,8], -80),([0,9], -20),([2,8], -40),([4,9], 4),([6,7], 20),([6,9], 8),([7,9], -20),([8,8], -40),([9,9], -16)]
def c3GroupHessian132_13 : Poly := List.flatten [c3GroupHessian132_13Chunk0]
theorem c3GroupHessian132_13_check : sumFast (c3TensorGroup132.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian132_13 := by kernel_rfl
private def c3GroupHessian132_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 80),([0,7], 40),([0,9], 32),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 40),([7,9], 40),([9,9], 16)]
def c3GroupHessian132_22 : Poly := List.flatten [c3GroupHessian132_22Chunk0]
theorem c3GroupHessian132_22_check : sumFast (c3TensorGroup132.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian132_22 := by kernel_rfl
private def c3GroupHessian132_23Chunk0 : Poly := [([0,0], -36),([0,3], -40),([0,4], -4),([0,5], -40),([0,6], -8),([0,8], -40),([0,9], 20),([3,8], -40),([4,9], -4),([5,8], -40),([6,7], -20),([6,9], -8),([7,9], 20),([9,9], 16)]
def c3GroupHessian132_23 : Poly := List.flatten [c3GroupHessian132_23Chunk0]
theorem c3GroupHessian132_23_check : sumFast (c3TensorGroup132.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian132_23 := by kernel_rfl
private def c3GroupHessian132_33Chunk0 : Poly := [([0,0], 48),([0,6], 8),([0,8], 80),([0,9], 8),([4,4], 8),([4,6], -8),([4,9], -8),([6,6], 16),([6,9], -16),([8,8], 40),([9,9], 16)]
def c3GroupHessian132_33 : Poly := List.flatten [c3GroupHessian132_33Chunk0]
theorem c3GroupHessian132_33_check : sumFast (c3TensorGroup132.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian132_33 := by kernel_rfl
end D4.Secondary
