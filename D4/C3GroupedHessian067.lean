import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup67_det_check : c3TensorGroup67.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 90)) = true := by kernel_rfl
private def c3GroupHessian67_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 80),([0,6], 32),([0,9], 32),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 16),([6,9], 32),([9,9], 16)]
def c3GroupHessian67_00 : Poly := List.flatten [c3GroupHessian67_00Chunk0]
theorem c3GroupHessian67_00_check : sumFast (c3TensorGroup67.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian67_00 := by kernel_rfl
private def c3GroupHessian67_01Chunk0 : Poly := [([0,0], 20),([0,2], 4),([0,6], 20),([0,7], 4),([0,8], -40),([0,9], 36),([1,8], -40),([2,6], 4),([2,9], 4),([5,8], -40),([6,7], 4),([6,9], 16),([7,9], 4),([9,9], 16)]
def c3GroupHessian67_01 : Poly := List.flatten [c3GroupHessian67_01Chunk0]
theorem c3GroupHessian67_01_check : sumFast (c3TensorGroup67.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian67_01 := by kernel_rfl
private def c3GroupHessian67_02Chunk0 : Poly := [([0,0], -56),([0,1], -40),([0,3], -8),([0,5], -80),([0,6], -16),([0,7], -4),([0,9], -32),([1,5], -40),([3,6], -8),([3,9], -8),([5,5], -40),([6,7], -4),([6,9], -16),([7,9], -4),([9,9], -16)]
def c3GroupHessian67_02 : Poly := List.flatten [c3GroupHessian67_02Chunk0]
theorem c3GroupHessian67_02_check : sumFast (c3TensorGroup67.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian67_02 := by kernel_rfl
private def c3GroupHessian67_03Chunk0 : Poly := [([0,0], 24),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -32),([0,8], 40),([0,9], -32),([1,4], 40),([1,8], 40),([4,5], 40),([5,8], 40),([6,6], -16),([6,9], -32),([9,9], -16)]
def c3GroupHessian67_03 : Poly := List.flatten [c3GroupHessian67_03Chunk0]
theorem c3GroupHessian67_03_check : sumFast (c3TensorGroup67.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian67_03 := by kernel_rfl
private def c3GroupHessian67_11Chunk0 : Poly := [([0,0], 32),([0,2], 24),([0,7], 24),([0,9], 40),([2,2], 8),([2,7], 16),([2,9], 8),([7,7], 8),([7,9], 8),([8,8], 40),([9,9], 16)]
def c3GroupHessian67_11 : Poly := List.flatten [c3GroupHessian67_11Chunk0]
theorem c3GroupHessian67_11_check : sumFast (c3TensorGroup67.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian67_11 := by kernel_rfl
private def c3GroupHessian67_12Chunk0 : Poly := [([0,0], -20),([0,2], -4),([0,3], -4),([0,7], -16),([0,8], 40),([0,9], -36),([2,3], 4),([2,7], -8),([2,9], -4),([3,7], 4),([3,9], -8),([5,8], 40),([7,7], -8),([7,9], -8),([9,9], -16)]
def c3GroupHessian67_12 : Poly := List.flatten [c3GroupHessian67_12Chunk0]
theorem c3GroupHessian67_12_check : sumFast (c3TensorGroup67.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian67_12 := by kernel_rfl
private def c3GroupHessian67_13Chunk0 : Poly := [([0,0], -20),([0,2], -4),([0,6], -20),([0,7], -4),([0,8], -40),([0,9], -36),([2,6], -4),([2,9], -4),([4,8], -40),([6,7], -4),([6,9], -16),([7,9], -4),([8,8], -40),([9,9], -16)]
def c3GroupHessian67_13 : Poly := List.flatten [c3GroupHessian67_13Chunk0]
theorem c3GroupHessian67_13_check : sumFast (c3TensorGroup67.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian67_13 := by kernel_rfl
private def c3GroupHessian67_22Chunk0 : Poly := [([0,0], 56),([0,3], 16),([0,5], 80),([0,7], 8),([0,9], 32),([3,3], 16),([3,7], -8),([3,9], 16),([5,5], 40),([7,7], 8),([7,9], 8),([9,9], 16)]
def c3GroupHessian67_22 : Poly := List.flatten [c3GroupHessian67_22Chunk0]
theorem c3GroupHessian67_22_check : sumFast (c3TensorGroup67.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian67_22 := by kernel_rfl
private def c3GroupHessian67_23Chunk0 : Poly := [([0,0], -24),([0,3], 8),([0,4], -40),([0,5], -40),([0,6], 16),([0,7], 4),([0,8], -40),([0,9], 32),([3,6], 8),([3,9], 8),([4,5], -40),([5,8], -40),([6,7], 4),([6,9], 16),([7,9], 4),([9,9], 16)]
def c3GroupHessian67_23 : Poly := List.flatten [c3GroupHessian67_23Chunk0]
theorem c3GroupHessian67_23_check : sumFast (c3TensorGroup67.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian67_23 := by kernel_rfl
private def c3GroupHessian67_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 32),([0,8], 80),([0,9], 32),([4,4], 40),([4,8], 80),([6,6], 16),([6,9], 32),([8,8], 40),([9,9], 16)]
def c3GroupHessian67_33 : Poly := List.flatten [c3GroupHessian67_33Chunk0]
theorem c3GroupHessian67_33_check : sumFast (c3TensorGroup67.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian67_33 := by kernel_rfl
end D4.Secondary
