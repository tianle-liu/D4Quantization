import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup36_det_check : c3TensorGroup36.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 53)) = true := by kernel_rfl
private def c3GroupHessian36_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 8),([0,6], 80),([0,9], 8),([1,1], 40),([1,6], 80),([5,5], 16),([5,9], -16),([6,6], 40),([9,9], 16)]
def c3GroupHessian36_00 : Poly := List.flatten [c3GroupHessian36_00Chunk0]
theorem c3GroupHessian36_00_check : sumFast (c3TensorGroup36.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian36_00 := by kernel_rfl
private def c3GroupHessian36_01Chunk0 : Poly := [([0,0], 12),([0,2], 8),([0,5], -4),([0,7], -40),([0,8], 4),([0,9], 24),([1,7], -40),([2,5], 4),([2,9], 4),([5,8], -8),([5,9], -8),([6,7], -40),([8,9], 16),([9,9], 16)]
def c3GroupHessian36_01 : Poly := List.flatten [c3GroupHessian36_01Chunk0]
theorem c3GroupHessian36_01_check : sumFast (c3TensorGroup36.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian36_01 := by kernel_rfl
private def c3GroupHessian36_02Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,3], 40),([0,5], -8),([0,6], 40),([0,7], 40),([0,9], -8),([1,3], 40),([1,7], 40),([3,6], 40),([5,5], -16),([5,9], 16),([6,7], 40),([9,9], -16)]
def c3GroupHessian36_02 : Poly := List.flatten [c3GroupHessian36_02Chunk0]
theorem c3GroupHessian36_02_check : sumFast (c3TensorGroup36.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian36_02 := by kernel_rfl
private def c3GroupHessian36_03Chunk0 : Poly := [([0,0], -44),([0,1], -40),([0,5], 8),([0,6], -80),([0,8], -4),([0,9], -20),([1,6], -40),([4,5], 20),([4,9], -20),([5,8], 8),([5,9], 8),([6,6], -40),([8,9], -16),([9,9], -16)]
def c3GroupHessian36_03 : Poly := List.flatten [c3GroupHessian36_03Chunk0]
theorem c3GroupHessian36_03_check : sumFast (c3TensorGroup36.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian36_03 := by kernel_rfl
private def c3GroupHessian36_11Chunk0 : Poly := [([0,0], 32),([0,2], 24),([0,8], 40),([0,9], 40),([2,2], 8),([2,8], 8),([2,9], 8),([7,7], 40),([8,8], 16),([8,9], 32),([9,9], 16)]
def c3GroupHessian36_11 : Poly := List.flatten [c3GroupHessian36_11Chunk0]
theorem c3GroupHessian36_11_check : sumFast (c3TensorGroup36.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian36_11 := by kernel_rfl
private def c3GroupHessian36_12Chunk0 : Poly := [([0,0], -12),([0,2], -8),([0,5], 4),([0,7], -40),([0,8], -4),([0,9], -24),([2,5], -4),([2,9], -4),([3,7], -40),([5,8], 8),([5,9], 8),([7,7], -40),([8,9], -16),([9,9], -16)]
def c3GroupHessian36_12 : Poly := List.flatten [c3GroupHessian36_12Chunk0]
theorem c3GroupHessian36_12_check : sumFast (c3TensorGroup36.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian36_12 := by kernel_rfl
private def c3GroupHessian36_13Chunk0 : Poly := [([0,0], -20),([0,2], -4),([0,4], -20),([0,7], 40),([0,8], -36),([0,9], -36),([2,8], -4),([2,9], -4),([4,8], -20),([4,9], -20),([6,7], 40),([8,8], -16),([8,9], -32),([9,9], -16)]
def c3GroupHessian36_13 : Poly := List.flatten [c3GroupHessian36_13Chunk0]
theorem c3GroupHessian36_13_check : sumFast (c3TensorGroup36.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian36_13 := by kernel_rfl
private def c3GroupHessian36_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 8),([0,7], 80),([0,9], 8),([3,3], 40),([3,7], 80),([5,5], 16),([5,9], -16),([7,7], 40),([9,9], 16)]
def c3GroupHessian36_22 : Poly := List.flatten [c3GroupHessian36_22Chunk0]
theorem c3GroupHessian36_22_check : sumFast (c3TensorGroup36.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian36_22 := by kernel_rfl
private def c3GroupHessian36_23Chunk0 : Poly := [([0,0], -36),([0,3], -40),([0,5], -8),([0,6], -40),([0,7], -40),([0,8], 4),([0,9], 20),([3,6], -40),([4,5], -20),([4,9], 20),([5,8], -8),([5,9], -8),([6,7], -40),([8,9], 16),([9,9], 16)]
def c3GroupHessian36_23 : Poly := List.flatten [c3GroupHessian36_23Chunk0]
theorem c3GroupHessian36_23_check : sumFast (c3TensorGroup36.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian36_23 := by kernel_rfl
private def c3GroupHessian36_33Chunk0 : Poly := [([0,0], 56),([0,4], 40),([0,6], 80),([0,8], 32),([0,9], 32),([4,4], 40),([4,8], 40),([4,9], 40),([6,6], 40),([8,8], 16),([8,9], 32),([9,9], 16)]
def c3GroupHessian36_33 : Poly := List.flatten [c3GroupHessian36_33Chunk0]
theorem c3GroupHessian36_33_check : sumFast (c3TensorGroup36.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian36_33 := by kernel_rfl
end D4.Secondary
