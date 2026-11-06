import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup54_det_check : c3TensorGroup54.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 76)) = true := by kernel_rfl
private def c3GroupHessian54_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 8),([0,6], 80),([0,9], 16),([1,1], 40),([1,6], 80),([5,5], 16),([5,9], 8),([6,6], 40),([9,9], 8)]
def c3GroupHessian54_00 : Poly := List.flatten [c3GroupHessian54_00Chunk0]
theorem c3GroupHessian54_00_check : sumFast (c3TensorGroup54.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian54_00 := by kernel_rfl
private def c3GroupHessian54_01Chunk0 : Poly := [([0,0], 12),([0,2], 4),([0,5], -4),([0,7], -40),([0,8], 8),([0,9], 20),([1,7], -40),([2,5], -8),([2,9], 4),([5,8], 4),([5,9], 4),([6,7], -40),([8,9], 8),([9,9], 8)]
def c3GroupHessian54_01 : Poly := List.flatten [c3GroupHessian54_01Chunk0]
theorem c3GroupHessian54_01_check : sumFast (c3TensorGroup54.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian54_01 := by kernel_rfl
private def c3GroupHessian54_02Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,3], 40),([0,5], -8),([0,6], 40),([0,7], 40),([0,9], -16),([1,3], 40),([1,7], 40),([3,6], 40),([5,5], -16),([5,9], -8),([6,7], 40),([9,9], -8)]
def c3GroupHessian54_02 : Poly := List.flatten [c3GroupHessian54_02Chunk0]
theorem c3GroupHessian54_02_check : sumFast (c3TensorGroup54.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian54_02 := by kernel_rfl
private def c3GroupHessian54_03Chunk0 : Poly := [([0,0], -48),([0,1], -40),([0,4], 4),([0,5], -4),([0,6], -80),([0,8], -8),([0,9], -16),([1,6], -40),([4,5], -8),([4,9], 4),([5,8], -4),([5,9], -4),([6,6], -40),([8,9], -8),([9,9], -8)]
def c3GroupHessian54_03 : Poly := List.flatten [c3GroupHessian54_03Chunk0]
theorem c3GroupHessian54_03_check : sumFast (c3TensorGroup54.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian54_03 := by kernel_rfl
private def c3GroupHessian54_11Chunk0 : Poly := [([0,0], 32),([0,2], 40),([0,8], 24),([0,9], 24),([2,2], 16),([2,8], 8),([2,9], 8),([7,7], 40),([8,8], 8),([8,9], 16),([9,9], 8)]
def c3GroupHessian54_11 : Poly := List.flatten [c3GroupHessian54_11Chunk0]
theorem c3GroupHessian54_11_check : sumFast (c3TensorGroup54.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian54_11 := by kernel_rfl
private def c3GroupHessian54_12Chunk0 : Poly := [([0,0], -12),([0,2], -4),([0,5], 4),([0,7], -40),([0,8], -8),([0,9], -20),([2,5], 8),([2,9], -4),([3,7], -40),([5,8], -4),([5,9], -4),([7,7], -40),([8,9], -8),([9,9], -8)]
def c3GroupHessian54_12 : Poly := List.flatten [c3GroupHessian54_12Chunk0]
theorem c3GroupHessian54_12_check : sumFast (c3TensorGroup54.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian54_12 := by kernel_rfl
private def c3GroupHessian54_13Chunk0 : Poly := [([0,0], -12),([0,2], -4),([0,4], 20),([0,7], 40),([0,8], -20),([0,9], -20),([2,4], 16),([2,8], -4),([2,9], -4),([4,8], 4),([4,9], 4),([6,7], 40),([8,8], -8),([8,9], -16),([9,9], -8)]
def c3GroupHessian54_13 : Poly := List.flatten [c3GroupHessian54_13Chunk0]
theorem c3GroupHessian54_13_check : sumFast (c3TensorGroup54.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian54_13 := by kernel_rfl
private def c3GroupHessian54_22Chunk0 : Poly := [([0,0], 48),([0,3], 80),([0,5], 8),([0,7], 80),([0,9], 16),([3,3], 40),([3,7], 80),([5,5], 16),([5,9], 8),([7,7], 40),([9,9], 8)]
def c3GroupHessian54_22 : Poly := List.flatten [c3GroupHessian54_22Chunk0]
theorem c3GroupHessian54_22_check : sumFast (c3TensorGroup54.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian54_22 := by kernel_rfl
private def c3GroupHessian54_23Chunk0 : Poly := [([0,0], -32),([0,3], -40),([0,4], -4),([0,5], 4),([0,6], -40),([0,7], -40),([0,8], 8),([0,9], 16),([3,6], -40),([4,5], 8),([4,9], -4),([5,8], 4),([5,9], 4),([6,7], -40),([8,9], 8),([9,9], 8)]
def c3GroupHessian54_23 : Poly := List.flatten [c3GroupHessian54_23Chunk0]
theorem c3GroupHessian54_23_check : sumFast (c3TensorGroup54.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian54_23 := by kernel_rfl
private def c3GroupHessian54_33Chunk0 : Poly := [([0,0], 48),([0,4], -8),([0,6], 80),([0,8], 16),([0,9], 16),([4,4], 16),([4,8], -8),([4,9], -8),([6,6], 40),([8,8], 8),([8,9], 16),([9,9], 8)]
def c3GroupHessian54_33 : Poly := List.flatten [c3GroupHessian54_33Chunk0]
theorem c3GroupHessian54_33_check : sumFast (c3TensorGroup54.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian54_33 := by kernel_rfl
end D4.Secondary
