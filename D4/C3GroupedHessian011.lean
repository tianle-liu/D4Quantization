import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup11_det_check : c3TensorGroup11.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 12)) = true := by kernel_rfl
private def c3GroupHessian11_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,6], 16),([0,9], 16),([1,1], 40),([5,5], 40),([6,6], 8),([6,9], 16),([9,9], 8)]
def c3GroupHessian11_00 : Poly := List.flatten [c3GroupHessian11_00Chunk0]
theorem c3GroupHessian11_00_check : sumFast (c3TensorGroup11.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian11_00 := by kernel_rfl
private def c3GroupHessian11_01Chunk0 : Poly := [([0,0], 48),([0,1], 40),([0,2], 40),([0,6], 8),([0,7], 4),([0,8], 4),([0,9], 16),([1,2], 40),([5,7], 20),([5,8], -20),([6,7], 4),([6,8], 4),([6,9], 8),([7,9], 4),([8,9], 4),([9,9], 8)]
def c3GroupHessian11_01 : Poly := List.flatten [c3GroupHessian11_01Chunk0]
theorem c3GroupHessian11_01_check : sumFast (c3TensorGroup11.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian11_01 := by kernel_rfl
private def c3GroupHessian11_02Chunk0 : Poly := [([0,0], -4),([0,3], 40),([0,5], -20),([0,6], -4),([0,7], -4),([0,9], -12),([1,3], 40),([5,5], -40),([5,7], -20),([6,7], -4),([6,9], -8),([7,9], -4),([9,9], -8)]
def c3GroupHessian11_02 : Poly := List.flatten [c3GroupHessian11_02Chunk0]
theorem c3GroupHessian11_02_check : sumFast (c3TensorGroup11.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian11_02 := by kernel_rfl
private def c3GroupHessian11_03Chunk0 : Poly := [([0,0], -12),([0,4], 40),([0,5], 20),([0,6], -20),([0,8], -4),([0,9], -20),([1,4], 40),([5,8], 20),([6,6], -8),([6,8], -4),([6,9], -16),([8,9], -4),([9,9], -8)]
def c3GroupHessian11_03 : Poly := List.flatten [c3GroupHessian11_03Chunk0]
theorem c3GroupHessian11_03_check : sumFast (c3TensorGroup11.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian11_03 := by kernel_rfl
private def c3GroupHessian11_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 8),([0,8], 8),([0,9], 16),([2,2], 40),([7,7], 16),([7,8], -16),([7,9], 8),([8,8], 16),([8,9], 8),([9,9], 8)]
def c3GroupHessian11_11 : Poly := List.flatten [c3GroupHessian11_11Chunk0]
theorem c3GroupHessian11_11_check : sumFast (c3TensorGroup11.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian11_11 := by kernel_rfl
private def c3GroupHessian11_12Chunk0 : Poly := [([0,0], -4),([0,3], 40),([0,7], -16),([0,8], 12),([0,9], -12),([2,3], 40),([5,7], -20),([5,8], 20),([7,7], -16),([7,8], 8),([7,9], -8),([8,9], -4),([9,9], -8)]
def c3GroupHessian11_12 : Poly := List.flatten [c3GroupHessian11_12Chunk0]
theorem c3GroupHessian11_12_check : sumFast (c3TensorGroup11.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian11_12 := by kernel_rfl
private def c3GroupHessian11_13Chunk0 : Poly := [([0,0], -12),([0,4], 40),([0,6], -8),([0,7], 4),([0,8], -24),([0,9], -20),([2,4], 40),([6,7], -4),([6,8], -4),([6,9], -8),([7,8], 8),([7,9], -4),([8,8], -16),([8,9], -8),([9,9], -8)]
def c3GroupHessian11_13 : Poly := List.flatten [c3GroupHessian11_13Chunk0]
theorem c3GroupHessian11_13_check : sumFast (c3TensorGroup11.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian11_13 := by kernel_rfl
private def c3GroupHessian11_22Chunk0 : Poly := [([0,0], 16),([0,5], 40),([0,7], 24),([0,9], 8),([3,3], 40),([5,5], 40),([5,7], 40),([7,7], 16),([7,9], 8),([9,9], 8)]
def c3GroupHessian11_22 : Poly := List.flatten [c3GroupHessian11_22Chunk0]
theorem c3GroupHessian11_22_check : sumFast (c3TensorGroup11.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian11_22 := by kernel_rfl
private def c3GroupHessian11_23Chunk0 : Poly := [([0,0], -8),([0,5], -20),([0,6], 4),([0,7], -4),([0,8], -12),([0,9], 16),([3,4], 40),([5,8], -20),([6,7], 4),([6,9], 8),([7,8], -8),([7,9], 4),([8,9], 4),([9,9], 8)]
def c3GroupHessian11_23 : Poly := List.flatten [c3GroupHessian11_23Chunk0]
theorem c3GroupHessian11_23_check : sumFast (c3TensorGroup11.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian11_23 := by kernel_rfl
private def c3GroupHessian11_33Chunk0 : Poly := [([0,0], 32),([0,6], 24),([0,8], 40),([0,9], 24),([4,4], 40),([6,6], 8),([6,8], 8),([6,9], 16),([8,8], 16),([8,9], 8),([9,9], 8)]
def c3GroupHessian11_33 : Poly := List.flatten [c3GroupHessian11_33Chunk0]
theorem c3GroupHessian11_33_check : sumFast (c3TensorGroup11.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian11_33 := by kernel_rfl
end D4.Secondary
