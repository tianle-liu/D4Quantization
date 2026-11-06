import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup41_det_check : c3TensorGroup41.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 59)) = true := by kernel_rfl
private def c3GroupHessian41_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 8),([0,6], 80),([0,9], 16),([1,1], 40),([1,6], 80),([5,5], 16),([5,9], 8),([6,6], 40),([9,9], 8)]
def c3GroupHessian41_00 : Poly := List.flatten [c3GroupHessian41_00Chunk0]
theorem c3GroupHessian41_00_check : sumFast (c3TensorGroup41.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian41_00 := by kernel_rfl
private def c3GroupHessian41_01Chunk0 : Poly := [([0,0], 8),([0,5], -16),([0,7], -40),([0,9], 16),([1,7], -40),([2,5], -20),([5,8], -20),([5,9], 4),([6,7], -40),([9,9], 8)]
def c3GroupHessian41_01 : Poly := List.flatten [c3GroupHessian41_01Chunk0]
theorem c3GroupHessian41_01_check : sumFast (c3TensorGroup41.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian41_01 := by kernel_rfl
private def c3GroupHessian41_02Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,3], 40),([0,5], -8),([0,6], 40),([0,7], 40),([0,9], -16),([1,3], 40),([1,7], 40),([3,6], 40),([5,5], -16),([5,9], -8),([6,7], 40),([9,9], -8)]
def c3GroupHessian41_02 : Poly := List.flatten [c3GroupHessian41_02Chunk0]
theorem c3GroupHessian41_02_check : sumFast (c3TensorGroup41.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian41_02 := by kernel_rfl
private def c3GroupHessian41_03Chunk0 : Poly := [([0,0], -44),([0,1], -40),([0,4], 4),([0,5], 8),([0,6], -80),([0,9], -12),([1,6], -40),([4,5], -8),([4,9], 4),([5,8], 20),([5,9], -4),([6,6], -40),([9,9], -8)]
def c3GroupHessian41_03 : Poly := List.flatten [c3GroupHessian41_03Chunk0]
theorem c3GroupHessian41_03_check : sumFast (c3TensorGroup41.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian41_03 := by kernel_rfl
private def c3GroupHessian41_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,8], 80),([0,9], 16),([2,2], 40),([2,8], 80),([7,7], 40),([8,8], 40),([9,9], 8)]
def c3GroupHessian41_11 : Poly := List.flatten [c3GroupHessian41_11Chunk0]
theorem c3GroupHessian41_11_check : sumFast (c3TensorGroup41.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian41_11 := by kernel_rfl
private def c3GroupHessian41_12Chunk0 : Poly := [([0,0], -8),([0,5], 16),([0,7], -40),([0,9], -16),([2,5], 20),([3,7], -40),([5,8], 20),([5,9], -4),([7,7], -40),([9,9], -8)]
def c3GroupHessian41_12 : Poly := List.flatten [c3GroupHessian41_12Chunk0]
theorem c3GroupHessian41_12_check : sumFast (c3TensorGroup41.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian41_12 := by kernel_rfl
private def c3GroupHessian41_13Chunk0 : Poly := [([0,0], -24),([0,2], -20),([0,4], 24),([0,7], 40),([0,8], -60),([0,9], -12),([2,4], 20),([2,8], -40),([4,8], 20),([4,9], 4),([6,7], 40),([8,8], -40),([9,9], -8)]
def c3GroupHessian41_13 : Poly := List.flatten [c3GroupHessian41_13Chunk0]
theorem c3GroupHessian41_13_check : sumFast (c3TensorGroup41.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian41_13 := by kernel_rfl
private def c3GroupHessian41_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 8),([0,7], 80),([0,9], 16),([3,3], 40),([3,7], 80),([5,5], 16),([5,9], 8),([7,7], 40),([9,9], 8)]
def c3GroupHessian41_22 : Poly := List.flatten [c3GroupHessian41_22Chunk0]
theorem c3GroupHessian41_22_check : sumFast (c3TensorGroup41.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian41_22 := by kernel_rfl
private def c3GroupHessian41_23Chunk0 : Poly := [([0,0], -36),([0,3], -40),([0,4], -4),([0,5], -8),([0,6], -40),([0,7], -40),([0,9], 12),([3,6], -40),([4,5], 8),([4,9], -4),([5,8], -20),([5,9], 4),([6,7], -40),([9,9], 8)]
def c3GroupHessian41_23 : Poly := List.flatten [c3GroupHessian41_23Chunk0]
theorem c3GroupHessian41_23_check : sumFast (c3TensorGroup41.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian41_23 := by kernel_rfl
private def c3GroupHessian41_33Chunk0 : Poly := [([0,0], 56),([0,4], -16),([0,6], 80),([0,8], 40),([0,9], 8),([4,4], 16),([4,8], -40),([4,9], -8),([6,6], 40),([8,8], 40),([9,9], 8)]
def c3GroupHessian41_33 : Poly := List.flatten [c3GroupHessian41_33Chunk0]
theorem c3GroupHessian41_33_check : sumFast (c3TensorGroup41.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian41_33 := by kernel_rfl
end D4.Secondary
