import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup2_det_check : c3TensorGroup2.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 3)) = true := by kernel_rfl
private def c3GroupHessian2_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 16),([0,6], 8),([0,9], 8),([1,1], 40),([5,5], 8),([5,6], 8),([5,9], 8),([6,6], 16),([6,9], -16),([9,9], 16)]
def c3GroupHessian2_00 : Poly := List.flatten [c3GroupHessian2_00Chunk0]
theorem c3GroupHessian2_00_check : sumFast (c3TensorGroup2.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian2_00 := by kernel_rfl
private def c3GroupHessian2_01Chunk0 : Poly := [([0,0], 44),([0,1], 40),([0,2], 40),([0,5], 4),([0,6], -8),([0,7], 4),([0,8], 4),([0,9], 20),([1,2], 40),([5,7], 4),([5,8], 4),([5,9], 4),([6,7], -8),([6,8], -8),([6,9], -8),([7,9], 16),([8,9], 16),([9,9], 16)]
def c3GroupHessian2_01 : Poly := List.flatten [c3GroupHessian2_01Chunk0]
theorem c3GroupHessian2_01_check : sumFast (c3TensorGroup2.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian2_01 := by kernel_rfl
private def c3GroupHessian2_02Chunk0 : Poly := [([0,0], -8),([0,3], 40),([0,5], -16),([0,6], 16),([0,7], -4),([0,9], -28),([1,3], 40),([5,5], -8),([5,6], -4),([5,7], -4),([5,9], -8),([6,7], 8),([6,9], 8),([7,9], -16),([9,9], -16)]
def c3GroupHessian2_02 : Poly := List.flatten [c3GroupHessian2_02Chunk0]
theorem c3GroupHessian2_02_check : sumFast (c3TensorGroup2.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian2_02 := by kernel_rfl
private def c3GroupHessian2_03Chunk0 : Poly := [([0,0], -4),([0,4], 40),([0,5], -4),([0,6], -16),([0,8], -4),([1,4], 40),([5,6], -4),([5,8], -4),([5,9], -4),([6,6], -16),([6,8], 8),([6,9], 16),([8,9], -16),([9,9], -16)]
def c3GroupHessian2_03 : Poly := List.flatten [c3GroupHessian2_03Chunk0]
theorem c3GroupHessian2_03_check : sumFast (c3TensorGroup2.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian2_03 := by kernel_rfl
private def c3GroupHessian2_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 32),([0,8], 32),([0,9], 32),([2,2], 40),([7,7], 16),([7,8], 32),([7,9], 32),([8,8], 16),([8,9], 32),([9,9], 16)]
def c3GroupHessian2_11 : Poly := List.flatten [c3GroupHessian2_11Chunk0]
theorem c3GroupHessian2_11_check : sumFast (c3TensorGroup2.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian2_11 := by kernel_rfl
private def c3GroupHessian2_12Chunk0 : Poly := [([0,0], -24),([0,3], 40),([0,5], -4),([0,7], -40),([0,8], -24),([0,9], -40),([2,3], 40),([5,7], -4),([5,8], -4),([5,9], -4),([7,7], -16),([7,8], -16),([7,9], -32),([8,9], -16),([9,9], -16)]
def c3GroupHessian2_12 : Poly := List.flatten [c3GroupHessian2_12Chunk0]
theorem c3GroupHessian2_12_check : sumFast (c3TensorGroup2.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian2_12 := by kernel_rfl
private def c3GroupHessian2_13Chunk0 : Poly := [([0,0], 4),([0,4], 40),([0,6], 8),([0,7], 4),([0,8], -12),([0,9], -12),([2,4], 40),([6,7], 8),([6,8], 8),([6,9], 8),([7,8], -16),([7,9], -16),([8,8], -16),([8,9], -32),([9,9], -16)]
def c3GroupHessian2_13 : Poly := List.flatten [c3GroupHessian2_13Chunk0]
theorem c3GroupHessian2_13_check : sumFast (c3TensorGroup2.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian2_13 := by kernel_rfl
private def c3GroupHessian2_22Chunk0 : Poly := [([0,0], 48),([0,5], 16),([0,7], 48),([0,9], 48),([3,3], 40),([5,5], 8),([5,7], 8),([5,9], 8),([7,7], 16),([7,9], 32),([9,9], 16)]
def c3GroupHessian2_22 : Poly := List.flatten [c3GroupHessian2_22Chunk0]
theorem c3GroupHessian2_22_check : sumFast (c3TensorGroup2.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian2_22 := by kernel_rfl
private def c3GroupHessian2_23Chunk0 : Poly := [([0,0], -16),([0,5], 4),([0,6], -16),([0,7], -4),([0,8], 24),([0,9], 20),([3,4], 40),([5,6], 4),([5,8], 4),([5,9], 4),([6,7], -8),([6,9], -8),([7,8], 16),([7,9], 16),([8,9], 16),([9,9], 16)]
def c3GroupHessian2_23 : Poly := List.flatten [c3GroupHessian2_23Chunk0]
theorem c3GroupHessian2_23_check : sumFast (c3TensorGroup2.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian2_23 := by kernel_rfl
private def c3GroupHessian2_33Chunk0 : Poly := [([0,0], 16),([0,6], 24),([0,8], -8),([0,9], -8),([4,4], 40),([6,6], 16),([6,8], -16),([6,9], -16),([8,8], 16),([8,9], 32),([9,9], 16)]
def c3GroupHessian2_33 : Poly := List.flatten [c3GroupHessian2_33Chunk0]
theorem c3GroupHessian2_33_check : sumFast (c3TensorGroup2.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian2_33 := by kernel_rfl
end D4.Secondary
