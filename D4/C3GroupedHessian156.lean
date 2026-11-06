import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup156_det_check : c3TensorGroup156.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 203)) = true := by kernel_rfl
private def c3GroupHessian156_00Chunk0 : Poly := [([0,0], 16),([0,1], 16),([0,5], 16),([0,9], 16),([1,1], 16),([1,5], 8),([1,9], -16),([5,5], 8),([5,9], 8),([6,6], 40),([9,9], 16)]
def c3GroupHessian156_00 : Poly := List.flatten [c3GroupHessian156_00Chunk0]
theorem c3GroupHessian156_00_check : sumFast (c3TensorGroup156.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian156_00 := by kernel_rfl
private def c3GroupHessian156_01Chunk0 : Poly := [([0,0], 8),([0,1], -8),([0,5], 4),([0,6], -40),([0,9], 24),([1,8], -20),([1,9], -8),([2,6], -40),([5,9], 4),([6,7], -40),([8,9], 20),([9,9], 16)]
def c3GroupHessian156_01 : Poly := List.flatten [c3GroupHessian156_01Chunk0]
theorem c3GroupHessian156_01_check : sumFast (c3TensorGroup156.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian156_01 := by kernel_rfl
private def c3GroupHessian156_02Chunk0 : Poly := [([0,0], -8),([0,1], 8),([0,3], 8),([0,5], -12),([0,6], 40),([0,9], -24),([1,3], 16),([1,5], -4),([1,9], 8),([3,5], 4),([3,9], -8),([5,5], -8),([5,9], -8),([6,7], 40),([9,9], -16)]
def c3GroupHessian156_02 : Poly := List.flatten [c3GroupHessian156_02Chunk0]
theorem c3GroupHessian156_02_check : sumFast (c3TensorGroup156.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian156_02 := by kernel_rfl
private def c3GroupHessian156_03Chunk0 : Poly := [([0,0], -8),([0,1], 8),([0,5], -4),([0,6], -40),([0,9], -24),([1,8], 20),([1,9], 8),([4,6], -40),([5,9], -4),([6,6], -40),([8,9], -20),([9,9], -16)]
def c3GroupHessian156_03 : Poly := List.flatten [c3GroupHessian156_03Chunk0]
theorem c3GroupHessian156_03_check : sumFast (c3TensorGroup156.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian156_03 := by kernel_rfl
private def c3GroupHessian156_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 80),([0,8], 40),([0,9], 32),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 40),([8,9], 40),([9,9], 16)]
def c3GroupHessian156_11 : Poly := List.flatten [c3GroupHessian156_11Chunk0]
theorem c3GroupHessian156_11_check : sumFast (c3TensorGroup156.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian156_11 := by kernel_rfl
private def c3GroupHessian156_12Chunk0 : Poly := [([0,0], -56),([0,2], -40),([0,3], -8),([0,5], -4),([0,7], -80),([0,8], -20),([0,9], -32),([2,7], -40),([3,8], -20),([3,9], -8),([5,9], -4),([7,7], -40),([8,9], -20),([9,9], -16)]
def c3GroupHessian156_12 : Poly := List.flatten [c3GroupHessian156_12Chunk0]
theorem c3GroupHessian156_12_check : sumFast (c3TensorGroup156.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian156_12 := by kernel_rfl
private def c3GroupHessian156_13Chunk0 : Poly := [([0,0], 24),([0,2], 40),([0,4], 40),([0,6], 40),([0,7], 40),([0,8], -40),([0,9], -32),([2,4], 40),([2,6], 40),([4,7], 40),([6,7], 40),([8,8], -40),([8,9], -40),([9,9], -16)]
def c3GroupHessian156_13 : Poly := List.flatten [c3GroupHessian156_13Chunk0]
theorem c3GroupHessian156_13_check : sumFast (c3TensorGroup156.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian156_13 := by kernel_rfl
private def c3GroupHessian156_22Chunk0 : Poly := [([0,0], 56),([0,3], 16),([0,5], 8),([0,7], 80),([0,9], 32),([3,3], 16),([3,5], -8),([3,9], 16),([5,5], 8),([5,9], 8),([7,7], 40),([9,9], 16)]
def c3GroupHessian156_22 : Poly := List.flatten [c3GroupHessian156_22Chunk0]
theorem c3GroupHessian156_22_check : sumFast (c3TensorGroup156.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian156_22 := by kernel_rfl
private def c3GroupHessian156_23Chunk0 : Poly := [([0,0], -24),([0,3], 8),([0,4], -40),([0,5], 4),([0,6], -40),([0,7], -40),([0,8], 20),([0,9], 32),([3,8], 20),([3,9], 8),([4,7], -40),([5,9], 4),([6,7], -40),([8,9], 20),([9,9], 16)]
def c3GroupHessian156_23 : Poly := List.flatten [c3GroupHessian156_23Chunk0]
theorem c3GroupHessian156_23_check : sumFast (c3TensorGroup156.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian156_23 := by kernel_rfl
private def c3GroupHessian156_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 80),([0,8], 40),([0,9], 32),([4,4], 40),([4,6], 80),([6,6], 40),([8,8], 40),([8,9], 40),([9,9], 16)]
def c3GroupHessian156_33 : Poly := List.flatten [c3GroupHessian156_33Chunk0]
theorem c3GroupHessian156_33_check : sumFast (c3TensorGroup156.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian156_33 := by kernel_rfl
end D4.Secondary
