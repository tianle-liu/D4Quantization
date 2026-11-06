import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup4_det_check : c3TensorGroup4.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 5)) = true := by kernel_rfl
private def c3GroupHessian4_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 32),([0,6], 40),([0,9], 8),([1,1], 40),([5,5], 16),([5,6], 40),([5,9], 8),([6,6], 40),([9,9], 8)]
def c3GroupHessian4_00 : Poly := List.flatten [c3GroupHessian4_00Chunk0]
theorem c3GroupHessian4_00_check : sumFast (c3TensorGroup4.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian4_00 := by kernel_rfl
private def c3GroupHessian4_01Chunk0 : Poly := [([0,0], 44),([0,1], 40),([0,2], 40),([0,5], 4),([0,7], -8),([0,8], 4),([0,9], 12),([1,2], 40),([5,7], -8),([5,8], 4),([5,9], 4),([6,7], -20),([7,9], 4),([8,9], 8),([9,9], 8)]
def c3GroupHessian4_01 : Poly := List.flatten [c3GroupHessian4_01Chunk0]
theorem c3GroupHessian4_01_check : sumFast (c3TensorGroup4.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian4_01 := by kernel_rfl
private def c3GroupHessian4_02Chunk0 : Poly := [([0,0], 4),([0,3], 40),([0,5], -12),([0,6], 20),([0,7], 8),([0,9], -8),([1,3], 40),([5,5], -16),([5,6], -20),([5,7], 8),([5,9], -8),([6,7], 20),([7,9], -4),([9,9], -8)]
def c3GroupHessian4_02 : Poly := List.flatten [c3GroupHessian4_02Chunk0]
theorem c3GroupHessian4_02_check : sumFast (c3TensorGroup4.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian4_02 := by kernel_rfl
private def c3GroupHessian4_03Chunk0 : Poly := [([0,0], -24),([0,4], 40),([0,5], -24),([0,6], -60),([0,8], -4),([0,9], -12),([1,4], 40),([5,6], -20),([5,8], -4),([5,9], -4),([6,6], -40),([8,9], -8),([9,9], -8)]
def c3GroupHessian4_03 : Poly := List.flatten [c3GroupHessian4_03Chunk0]
theorem c3GroupHessian4_03_check : sumFast (c3TensorGroup4.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian4_03 := by kernel_rfl
private def c3GroupHessian4_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 8),([0,8], 16),([0,9], 16),([2,2], 40),([7,7], 16),([7,8], 8),([7,9], 8),([8,8], 8),([8,9], 16),([9,9], 8)]
def c3GroupHessian4_11 : Poly := List.flatten [c3GroupHessian4_11Chunk0]
theorem c3GroupHessian4_11_check : sumFast (c3TensorGroup4.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian4_11 := by kernel_rfl
private def c3GroupHessian4_12Chunk0 : Poly := [([0,0], -4),([0,3], 40),([0,5], -4),([0,7], -16),([0,8], -4),([0,9], -12),([2,3], 40),([5,7], 8),([5,8], -4),([5,9], -4),([7,7], -16),([7,8], -4),([7,9], -8),([8,9], -8),([9,9], -8)]
def c3GroupHessian4_12 : Poly := List.flatten [c3GroupHessian4_12Chunk0]
theorem c3GroupHessian4_12_check : sumFast (c3TensorGroup4.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian4_12 := by kernel_rfl
private def c3GroupHessian4_13Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,7], 16),([0,8], -16),([0,9], -16),([2,4], 40),([6,7], 20),([7,8], -4),([7,9], -4),([8,8], -8),([8,9], -16),([9,9], -8)]
def c3GroupHessian4_13 : Poly := List.flatten [c3GroupHessian4_13Chunk0]
theorem c3GroupHessian4_13_check : sumFast (c3TensorGroup4.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian4_13 := by kernel_rfl
private def c3GroupHessian4_22Chunk0 : Poly := [([0,0], 16),([0,5], -8),([0,7], 24),([0,9], 8),([3,3], 40),([5,5], 16),([5,7], -16),([5,9], 8),([7,7], 16),([7,9], 8),([9,9], 8)]
def c3GroupHessian4_22 : Poly := List.flatten [c3GroupHessian4_22Chunk0]
theorem c3GroupHessian4_22_check : sumFast (c3TensorGroup4.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian4_22 := by kernel_rfl
private def c3GroupHessian4_23Chunk0 : Poly := [([0,0], -16),([0,5], 24),([0,6], -20),([0,7], -16),([0,8], 4),([0,9], 12),([3,4], 40),([5,6], 20),([5,8], 4),([5,9], 4),([6,7], -20),([7,8], 4),([7,9], 4),([8,9], 8),([9,9], 8)]
def c3GroupHessian4_23 : Poly := List.flatten [c3GroupHessian4_23Chunk0]
theorem c3GroupHessian4_23_check : sumFast (c3TensorGroup4.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian4_23 := by kernel_rfl
private def c3GroupHessian4_33Chunk0 : Poly := [([0,0], 48),([0,6], 80),([0,8], 16),([0,9], 16),([4,4], 40),([6,6], 40),([8,8], 8),([8,9], 16),([9,9], 8)]
def c3GroupHessian4_33 : Poly := List.flatten [c3GroupHessian4_33Chunk0]
theorem c3GroupHessian4_33_check : sumFast (c3TensorGroup4.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian4_33 := by kernel_rfl
end D4.Secondary
