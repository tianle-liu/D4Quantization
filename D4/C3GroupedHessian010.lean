import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup10_det_check : c3TensorGroup10.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 11)) = true := by kernel_rfl
private def c3GroupHessian10_00Chunk0 : Poly := [([0,0], 56),([0,1], 80),([0,5], 40),([0,6], 8),([0,9], 32),([1,1], 40),([5,5], 40),([5,9], 40),([6,6], 8),([6,9], 8),([9,9], 16)]
def c3GroupHessian10_00 : Poly := List.flatten [c3GroupHessian10_00Chunk0]
theorem c3GroupHessian10_00_check : sumFast (c3TensorGroup10.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian10_00 := by kernel_rfl
private def c3GroupHessian10_01Chunk0 : Poly := [([0,0], 56),([0,1], 40),([0,2], 40),([0,5], 20),([0,6], 4),([0,7], 20),([0,8], -8),([0,9], 32),([1,2], 40),([5,7], 40),([5,8], -20),([5,9], 20),([6,8], 4),([6,9], 4),([7,9], 20),([8,9], -8),([9,9], 16)]
def c3GroupHessian10_01 : Poly := List.flatten [c3GroupHessian10_01Chunk0]
theorem c3GroupHessian10_01_check : sumFast (c3TensorGroup10.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian10_01 := by kernel_rfl
private def c3GroupHessian10_02Chunk0 : Poly := [([0,0], -24),([0,3], 40),([0,5], -60),([0,7], -20),([0,9], -40),([1,3], 40),([5,5], -40),([5,7], -40),([5,9], -40),([6,9], -4),([7,9], -20),([9,9], -16)]
def c3GroupHessian10_02 : Poly := List.flatten [c3GroupHessian10_02Chunk0]
theorem c3GroupHessian10_02_check : sumFast (c3TensorGroup10.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian10_02 := by kernel_rfl
private def c3GroupHessian10_03Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,6], -12),([0,8], 8),([0,9], -24),([1,4], 40),([5,8], 20),([5,9], -20),([6,6], -8),([6,8], -4),([6,9], -8),([8,9], 8),([9,9], -16)]
def c3GroupHessian10_03 : Poly := List.flatten [c3GroupHessian10_03Chunk0]
theorem c3GroupHessian10_03_check : sumFast (c3TensorGroup10.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian10_03 := by kernel_rfl
private def c3GroupHessian10_11Chunk0 : Poly := [([0,0], 56),([0,2], 80),([0,7], 40),([0,8], -16),([0,9], 32),([2,2], 40),([7,7], 40),([7,8], -40),([7,9], 40),([8,8], 16),([8,9], -16),([9,9], 16)]
def c3GroupHessian10_11 : Poly := List.flatten [c3GroupHessian10_11Chunk0]
theorem c3GroupHessian10_11_check : sumFast (c3TensorGroup10.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian10_11 := by kernel_rfl
private def c3GroupHessian10_12Chunk0 : Poly := [([0,0], -24),([0,3], 40),([0,5], -20),([0,7], -60),([0,8], 24),([0,9], -40),([2,3], 40),([5,7], -40),([5,8], 20),([5,9], -20),([7,7], -40),([7,8], 20),([7,9], -40),([8,9], 8),([9,9], -16)]
def c3GroupHessian10_12 : Poly := List.flatten [c3GroupHessian10_12Chunk0]
theorem c3GroupHessian10_12_check : sumFast (c3TensorGroup10.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian10_12 := by kernel_rfl
private def c3GroupHessian10_13Chunk0 : Poly := [([0,0], -8),([0,4], 40),([0,6], -4),([0,9], -24),([2,4], 40),([6,8], -4),([6,9], -4),([7,8], 20),([7,9], -20),([8,8], -16),([8,9], 16),([9,9], -16)]
def c3GroupHessian10_13 : Poly := List.flatten [c3GroupHessian10_13Chunk0]
theorem c3GroupHessian10_13_check : sumFast (c3TensorGroup10.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian10_13 := by kernel_rfl
private def c3GroupHessian10_22Chunk0 : Poly := [([0,0], 48),([0,5], 80),([0,7], 80),([0,9], 48),([3,3], 40),([5,5], 40),([5,7], 80),([5,9], 40),([7,7], 40),([7,9], 40),([9,9], 16)]
def c3GroupHessian10_22 : Poly := List.flatten [c3GroupHessian10_22Chunk0]
theorem c3GroupHessian10_22_check : sumFast (c3TensorGroup10.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian10_22 := by kernel_rfl
private def c3GroupHessian10_23Chunk0 : Poly := [([0,8], -24),([0,9], 32),([3,4], 40),([5,8], -20),([5,9], 20),([6,9], 4),([7,8], -20),([7,9], 20),([8,9], -8),([9,9], 16)]
def c3GroupHessian10_23 : Poly := List.flatten [c3GroupHessian10_23Chunk0]
theorem c3GroupHessian10_23_check : sumFast (c3TensorGroup10.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian10_23 := by kernel_rfl
private def c3GroupHessian10_33Chunk0 : Poly := [([0,0], 16),([0,6], 16),([0,8], 16),([0,9], 16),([4,4], 40),([6,6], 8),([6,8], 8),([6,9], 8),([8,8], 16),([8,9], -16),([9,9], 16)]
def c3GroupHessian10_33 : Poly := List.flatten [c3GroupHessian10_33Chunk0]
theorem c3GroupHessian10_33_check : sumFast (c3TensorGroup10.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian10_33 := by kernel_rfl
end D4.Secondary
