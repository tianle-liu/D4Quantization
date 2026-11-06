import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup62_det_check : c3TensorGroup62.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 85)) = true := by kernel_rfl
private def c3GroupHessian62_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 80),([0,6], 8),([0,9], 16),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 16),([6,9], 8),([9,9], 8)]
def c3GroupHessian62_00 : Poly := List.flatten [c3GroupHessian62_00Chunk0]
theorem c3GroupHessian62_00_check : sumFast (c3TensorGroup62.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian62_00 := by kernel_rfl
private def c3GroupHessian62_01Chunk0 : Poly := [([0,0], 8),([0,6], -16),([0,8], -40),([0,9], 16),([1,8], -40),([2,6], -20),([5,8], -40),([6,7], -20),([6,9], 4),([9,9], 8)]
def c3GroupHessian62_01 : Poly := List.flatten [c3GroupHessian62_01Chunk0]
theorem c3GroupHessian62_01_check : sumFast (c3TensorGroup62.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian62_01 := by kernel_rfl
private def c3GroupHessian62_02Chunk0 : Poly := [([0,0], -44),([0,1], -40),([0,3], 4),([0,5], -80),([0,6], 8),([0,9], -12),([1,5], -40),([3,6], -8),([3,9], 4),([5,5], -40),([6,7], 20),([6,9], -4),([9,9], -8)]
def c3GroupHessian62_02 : Poly := List.flatten [c3GroupHessian62_02Chunk0]
theorem c3GroupHessian62_02_check : sumFast (c3TensorGroup62.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian62_02 := by kernel_rfl
private def c3GroupHessian62_03Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -8),([0,8], 40),([0,9], -16),([1,4], 40),([1,8], 40),([4,5], 40),([5,8], 40),([6,6], -16),([6,9], -8),([9,9], -8)]
def c3GroupHessian62_03 : Poly := List.flatten [c3GroupHessian62_03Chunk0]
theorem c3GroupHessian62_03_check : sumFast (c3TensorGroup62.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian62_03 := by kernel_rfl
private def c3GroupHessian62_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 80),([0,9], 16),([2,2], 40),([2,7], 80),([7,7], 40),([8,8], 40),([9,9], 8)]
def c3GroupHessian62_11 : Poly := List.flatten [c3GroupHessian62_11Chunk0]
theorem c3GroupHessian62_11_check : sumFast (c3TensorGroup62.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian62_11 := by kernel_rfl
private def c3GroupHessian62_12Chunk0 : Poly := [([0,0], -24),([0,2], -20),([0,3], 24),([0,7], -60),([0,8], 40),([0,9], -12),([2,3], 20),([2,7], -40),([3,7], 20),([3,9], 4),([5,8], 40),([7,7], -40),([9,9], -8)]
def c3GroupHessian62_12 : Poly := List.flatten [c3GroupHessian62_12Chunk0]
theorem c3GroupHessian62_12_check : sumFast (c3TensorGroup62.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian62_12 := by kernel_rfl
private def c3GroupHessian62_13Chunk0 : Poly := [([0,0], -8),([0,6], 16),([0,8], -40),([0,9], -16),([2,6], 20),([4,8], -40),([6,7], 20),([6,9], -4),([8,8], -40),([9,9], -8)]
def c3GroupHessian62_13 : Poly := List.flatten [c3GroupHessian62_13Chunk0]
theorem c3GroupHessian62_13_check : sumFast (c3TensorGroup62.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian62_13 := by kernel_rfl
private def c3GroupHessian62_22Chunk0 : Poly := [([0,0], 56),([0,3], -16),([0,5], 80),([0,7], 40),([0,9], 8),([3,3], 16),([3,7], -40),([3,9], -8),([5,5], 40),([7,7], 40),([9,9], 8)]
def c3GroupHessian62_22 : Poly := List.flatten [c3GroupHessian62_22Chunk0]
theorem c3GroupHessian62_22_check : sumFast (c3TensorGroup62.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian62_22 := by kernel_rfl
private def c3GroupHessian62_23Chunk0 : Poly := [([0,0], -36),([0,3], -4),([0,4], -40),([0,5], -40),([0,6], -8),([0,8], -40),([0,9], 12),([3,6], 8),([3,9], -4),([4,5], -40),([5,8], -40),([6,7], -20),([6,9], 4),([9,9], 8)]
def c3GroupHessian62_23 : Poly := List.flatten [c3GroupHessian62_23Chunk0]
theorem c3GroupHessian62_23_check : sumFast (c3TensorGroup62.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian62_23 := by kernel_rfl
private def c3GroupHessian62_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 8),([0,8], 80),([0,9], 16),([4,4], 40),([4,8], 80),([6,6], 16),([6,9], 8),([8,8], 40),([9,9], 8)]
def c3GroupHessian62_33 : Poly := List.flatten [c3GroupHessian62_33Chunk0]
theorem c3GroupHessian62_33_check : sumFast (c3TensorGroup62.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian62_33 := by kernel_rfl
end D4.Secondary
