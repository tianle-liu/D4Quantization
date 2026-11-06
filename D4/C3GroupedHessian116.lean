import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup116_det_check : c3TensorGroup116.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 153)) = true := by kernel_rfl
private def c3GroupHessian116_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,6], 80),([0,9], 16),([1,1], 40),([1,6], 80),([5,5], 40),([6,6], 40),([9,9], 8)]
def c3GroupHessian116_00 : Poly := List.flatten [c3GroupHessian116_00Chunk0]
theorem c3GroupHessian116_00_check : sumFast (c3TensorGroup116.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian116_00 := by kernel_rfl
private def c3GroupHessian116_01Chunk0 : Poly := [([0,0], 8),([0,5], -40),([0,7], -16),([0,9], 16),([1,7], -20),([2,5], -40),([5,8], -40),([6,7], -20),([7,9], 4),([9,9], 8)]
def c3GroupHessian116_01 : Poly := List.flatten [c3GroupHessian116_01Chunk0]
theorem c3GroupHessian116_01_check : sumFast (c3TensorGroup116.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian116_01 := by kernel_rfl
private def c3GroupHessian116_02Chunk0 : Poly := [([0,0], -8),([0,5], -40),([0,7], 16),([0,9], -16),([1,7], 20),([3,5], -40),([5,5], -40),([6,7], 20),([7,9], -4),([9,9], -8)]
def c3GroupHessian116_02 : Poly := List.flatten [c3GroupHessian116_02Chunk0]
theorem c3GroupHessian116_02_check : sumFast (c3TensorGroup116.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian116_02 := by kernel_rfl
private def c3GroupHessian116_03Chunk0 : Poly := [([0,0], -24),([0,1], -20),([0,4], 24),([0,5], 40),([0,6], -60),([0,9], -12),([1,4], 20),([1,6], -40),([4,6], 20),([4,9], 4),([5,8], 40),([6,6], -40),([9,9], -8)]
def c3GroupHessian116_03 : Poly := List.flatten [c3GroupHessian116_03Chunk0]
theorem c3GroupHessian116_03_check : sumFast (c3TensorGroup116.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian116_03 := by kernel_rfl
private def c3GroupHessian116_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 8),([0,8], 80),([0,9], 16),([2,2], 40),([2,8], 80),([7,7], 16),([7,9], 8),([8,8], 40),([9,9], 8)]
def c3GroupHessian116_11 : Poly := List.flatten [c3GroupHessian116_11Chunk0]
theorem c3GroupHessian116_11_check : sumFast (c3TensorGroup116.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian116_11 := by kernel_rfl
private def c3GroupHessian116_12Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,3], 40),([0,5], 40),([0,7], -8),([0,8], 40),([0,9], -16),([2,3], 40),([2,5], 40),([3,8], 40),([5,8], 40),([7,7], -16),([7,9], -8),([9,9], -8)]
def c3GroupHessian116_12 : Poly := List.flatten [c3GroupHessian116_12Chunk0]
theorem c3GroupHessian116_12_check : sumFast (c3TensorGroup116.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian116_12 := by kernel_rfl
private def c3GroupHessian116_13Chunk0 : Poly := [([0,0], -44),([0,2], -40),([0,4], 4),([0,7], 8),([0,8], -80),([0,9], -12),([2,8], -40),([4,7], -8),([4,9], 4),([6,7], 20),([7,9], -4),([8,8], -40),([9,9], -8)]
def c3GroupHessian116_13 : Poly := List.flatten [c3GroupHessian116_13Chunk0]
theorem c3GroupHessian116_13_check : sumFast (c3TensorGroup116.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian116_13 := by kernel_rfl
private def c3GroupHessian116_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 80),([0,7], 8),([0,9], 16),([3,3], 40),([3,5], 80),([5,5], 40),([7,7], 16),([7,9], 8),([9,9], 8)]
def c3GroupHessian116_22 : Poly := List.flatten [c3GroupHessian116_22Chunk0]
theorem c3GroupHessian116_22_check : sumFast (c3TensorGroup116.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian116_22 := by kernel_rfl
private def c3GroupHessian116_23Chunk0 : Poly := [([0,0], -36),([0,3], -40),([0,4], -4),([0,5], -40),([0,7], -8),([0,8], -40),([0,9], 12),([3,8], -40),([4,7], 8),([4,9], -4),([5,8], -40),([6,7], -20),([7,9], 4),([9,9], 8)]
def c3GroupHessian116_23 : Poly := List.flatten [c3GroupHessian116_23Chunk0]
theorem c3GroupHessian116_23_check : sumFast (c3TensorGroup116.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian116_23 := by kernel_rfl
private def c3GroupHessian116_33Chunk0 : Poly := [([0,0], 56),([0,4], -16),([0,6], 40),([0,8], 80),([0,9], 8),([4,4], 16),([4,6], -40),([4,9], -8),([6,6], 40),([8,8], 40),([9,9], 8)]
def c3GroupHessian116_33 : Poly := List.flatten [c3GroupHessian116_33Chunk0]
theorem c3GroupHessian116_33_check : sumFast (c3TensorGroup116.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian116_33 := by kernel_rfl
end D4.Secondary
