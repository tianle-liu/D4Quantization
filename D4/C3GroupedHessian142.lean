import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup142_det_check : c3TensorGroup142.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 184)) = true := by kernel_rfl
private def c3GroupHessian142_00Chunk0 : Poly := [([0,0], 32),([0,1], 24),([0,5], 40),([0,9], 40),([1,1], 8),([1,5], 8),([1,9], 8),([5,5], 16),([5,9], 32),([6,6], 40),([9,9], 16)]
def c3GroupHessian142_00 : Poly := List.flatten [c3GroupHessian142_00Chunk0]
theorem c3GroupHessian142_00_check : sumFast (c3TensorGroup142.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian142_00 := by kernel_rfl
private def c3GroupHessian142_01Chunk0 : Poly := [([0,0], 12),([0,1], 8),([0,5], 4),([0,6], -40),([0,8], -4),([0,9], 24),([1,8], 4),([1,9], 4),([2,6], -40),([5,8], -8),([5,9], 16),([6,7], -40),([8,9], -8),([9,9], 16)]
def c3GroupHessian142_01 : Poly := List.flatten [c3GroupHessian142_01Chunk0]
theorem c3GroupHessian142_01_check : sumFast (c3TensorGroup142.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian142_01 := by kernel_rfl
private def c3GroupHessian142_02Chunk0 : Poly := [([0,0], -20),([0,1], -4),([0,3], -20),([0,5], -36),([0,6], 40),([0,9], -36),([1,5], -4),([1,9], -4),([3,5], -20),([3,9], -20),([5,5], -16),([5,9], -32),([6,7], 40),([9,9], -16)]
def c3GroupHessian142_02 : Poly := List.flatten [c3GroupHessian142_02Chunk0]
theorem c3GroupHessian142_02_check : sumFast (c3TensorGroup142.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian142_02 := by kernel_rfl
private def c3GroupHessian142_03Chunk0 : Poly := [([0,0], -12),([0,1], -8),([0,5], -4),([0,6], -40),([0,8], 4),([0,9], -24),([1,8], -4),([1,9], -4),([4,6], -40),([5,8], 8),([5,9], -16),([6,6], -40),([8,9], 8),([9,9], -16)]
def c3GroupHessian142_03 : Poly := List.flatten [c3GroupHessian142_03Chunk0]
theorem c3GroupHessian142_03_check : sumFast (c3TensorGroup142.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian142_03 := by kernel_rfl
private def c3GroupHessian142_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 80),([0,8], 8),([0,9], 8),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 16),([8,9], -16),([9,9], 16)]
def c3GroupHessian142_11 : Poly := List.flatten [c3GroupHessian142_11Chunk0]
theorem c3GroupHessian142_11_check : sumFast (c3TensorGroup142.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian142_11 := by kernel_rfl
private def c3GroupHessian142_12Chunk0 : Poly := [([0,0], -44),([0,2], -40),([0,5], -4),([0,7], -80),([0,8], 8),([0,9], -20),([2,7], -40),([3,8], 20),([3,9], -20),([5,8], 8),([5,9], -16),([7,7], -40),([8,9], 8),([9,9], -16)]
def c3GroupHessian142_12 : Poly := List.flatten [c3GroupHessian142_12Chunk0]
theorem c3GroupHessian142_12_check : sumFast (c3TensorGroup142.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian142_12 := by kernel_rfl
private def c3GroupHessian142_13Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -8),([0,9], -8),([2,4], 40),([2,6], 40),([4,7], 40),([6,7], 40),([8,8], -16),([8,9], 16),([9,9], -16)]
def c3GroupHessian142_13 : Poly := List.flatten [c3GroupHessian142_13Chunk0]
theorem c3GroupHessian142_13_check : sumFast (c3TensorGroup142.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian142_13 := by kernel_rfl
private def c3GroupHessian142_22Chunk0 : Poly := [([0,0], 56),([0,3], 40),([0,5], 32),([0,7], 80),([0,9], 32),([3,3], 40),([3,5], 40),([3,9], 40),([5,5], 16),([5,9], 32),([7,7], 40),([9,9], 16)]
def c3GroupHessian142_22 : Poly := List.flatten [c3GroupHessian142_22Chunk0]
theorem c3GroupHessian142_22_check : sumFast (c3TensorGroup142.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian142_22 := by kernel_rfl
private def c3GroupHessian142_23Chunk0 : Poly := [([0,0], -36),([0,4], -40),([0,5], 4),([0,6], -40),([0,7], -40),([0,8], -8),([0,9], 20),([3,8], -20),([3,9], 20),([4,7], -40),([5,8], -8),([5,9], 16),([6,7], -40),([8,9], -8),([9,9], 16)]
def c3GroupHessian142_23 : Poly := List.flatten [c3GroupHessian142_23Chunk0]
theorem c3GroupHessian142_23_check : sumFast (c3TensorGroup142.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian142_23 := by kernel_rfl
private def c3GroupHessian142_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 80),([0,8], 8),([0,9], 8),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 16),([8,9], -16),([9,9], 16)]
def c3GroupHessian142_33 : Poly := List.flatten [c3GroupHessian142_33Chunk0]
theorem c3GroupHessian142_33_check : sumFast (c3TensorGroup142.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian142_33 := by kernel_rfl
end D4.Secondary
