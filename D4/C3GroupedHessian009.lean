import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup9_det_check : c3TensorGroup9.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 10)) = true := by kernel_rfl
private def c3GroupHessian9_00Chunk0 : Poly := [([0,0], 80),([0,1], 80),([0,5], 80),([0,6], 80),([0,9], 40),([1,1], 40),([5,5], 40),([5,6], 80),([5,9], 40),([6,6], 40),([6,9], 40),([9,9], 16)]
def c3GroupHessian9_00 : Poly := List.flatten [c3GroupHessian9_00Chunk0]
theorem c3GroupHessian9_00_check : sumFast (c3TensorGroup9.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian9_00 := by kernel_rfl
private def c3GroupHessian9_01Chunk0 : Poly := [([0,0], 40),([0,1], 40),([0,2], 40),([0,8], -20),([0,9], 24),([1,2], 40),([5,8], -20),([5,9], 20),([6,8], -20),([6,9], 20),([7,9], 4),([8,9], -8),([9,9], 16)]
def c3GroupHessian9_01 : Poly := List.flatten [c3GroupHessian9_01Chunk0]
theorem c3GroupHessian9_01_check : sumFast (c3TensorGroup9.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian9_01 := by kernel_rfl
private def c3GroupHessian9_02Chunk0 : Poly := [([0,0], -20),([0,3], 40),([0,5], -60),([0,6], -20),([0,9], -32),([1,3], 40),([5,5], -40),([5,6], -40),([5,9], -40),([6,9], -20),([7,9], -4),([9,9], -16)]
def c3GroupHessian9_02 : Poly := List.flatten [c3GroupHessian9_02Chunk0]
theorem c3GroupHessian9_02_check : sumFast (c3TensorGroup9.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian9_02 := by kernel_rfl
private def c3GroupHessian9_03Chunk0 : Poly := [([0,0], -20),([0,4], 40),([0,5], -20),([0,6], -60),([0,8], 20),([0,9], -32),([1,4], 40),([5,6], -40),([5,8], 20),([5,9], -20),([6,6], -40),([6,8], 20),([6,9], -40),([8,9], 8),([9,9], -16)]
def c3GroupHessian9_03 : Poly := List.flatten [c3GroupHessian9_03Chunk0]
theorem c3GroupHessian9_03_check : sumFast (c3TensorGroup9.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian9_03 := by kernel_rfl
private def c3GroupHessian9_11Chunk0 : Poly := [([0,0], 48),([0,2], 80),([0,7], 16),([0,8], 8),([0,9], 8),([2,2], 40),([7,7], 8),([7,8], 8),([7,9], 8),([8,8], 16),([8,9], -16),([9,9], 16)]
def c3GroupHessian9_11 : Poly := List.flatten [c3GroupHessian9_11Chunk0]
theorem c3GroupHessian9_11_check : sumFast (c3TensorGroup9.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian9_11 := by kernel_rfl
private def c3GroupHessian9_12Chunk0 : Poly := [([0,0], -4),([0,3], 40),([0,7], -12),([0,8], 12),([0,9], -16),([2,3], 40),([5,8], 20),([5,9], -20),([7,7], -8),([7,8], -4),([7,9], -8),([8,9], 8),([9,9], -16)]
def c3GroupHessian9_12 : Poly := List.flatten [c3GroupHessian9_12Chunk0]
theorem c3GroupHessian9_12_check : sumFast (c3TensorGroup9.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian9_12 := by kernel_rfl
private def c3GroupHessian9_13Chunk0 : Poly := [([0,0], -4),([0,4], 40),([0,7], -4),([0,9], -16),([2,4], 40),([6,8], 20),([6,9], -20),([7,8], -4),([7,9], -4),([8,8], -16),([8,9], 16),([9,9], -16)]
def c3GroupHessian9_13 : Poly := List.flatten [c3GroupHessian9_13Chunk0]
theorem c3GroupHessian9_13_check : sumFast (c3TensorGroup9.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian9_13 := by kernel_rfl
private def c3GroupHessian9_22Chunk0 : Poly := [([0,0], 16),([0,5], 40),([0,7], 8),([0,9], 24),([3,3], 40),([5,5], 40),([5,9], 40),([7,7], 8),([7,9], 8),([9,9], 16)]
def c3GroupHessian9_22 : Poly := List.flatten [c3GroupHessian9_22Chunk0]
theorem c3GroupHessian9_22_check : sumFast (c3TensorGroup9.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian9_22 := by kernel_rfl
private def c3GroupHessian9_23Chunk0 : Poly := [([0,0], 8),([0,5], 20),([0,6], 20),([0,7], 4),([0,8], -12),([0,9], 24),([3,4], 40),([5,6], 40),([5,8], -20),([5,9], 20),([6,9], 20),([7,8], 4),([7,9], 4),([8,9], -8),([9,9], 16)]
def c3GroupHessian9_23 : Poly := List.flatten [c3GroupHessian9_23Chunk0]
theorem c3GroupHessian9_23_check : sumFast (c3TensorGroup9.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian9_23 := by kernel_rfl
private def c3GroupHessian9_33Chunk0 : Poly := [([0,0], 16),([0,6], 40),([0,8], -8),([0,9], 24),([4,4], 40),([6,6], 40),([6,8], -40),([6,9], 40),([8,8], 16),([8,9], -16),([9,9], 16)]
def c3GroupHessian9_33 : Poly := List.flatten [c3GroupHessian9_33Chunk0]
theorem c3GroupHessian9_33_check : sumFast (c3TensorGroup9.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian9_33 := by kernel_rfl
end D4.Secondary
