import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup74_det_check : c3TensorGroup74.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 101)) = true := by kernel_rfl
private def c3GroupHessian74_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 80),([0,6], 16),([0,9], 8),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 8),([6,9], 8),([9,9], 16)]
def c3GroupHessian74_00 : Poly := List.flatten [c3GroupHessian74_00Chunk0]
theorem c3GroupHessian74_00_check : sumFast (c3TensorGroup74.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian74_00 := by kernel_rfl
private def c3GroupHessian74_01Chunk0 : Poly := [([0,0], 4),([0,2], 4),([0,6], 4),([0,8], -40),([0,9], 16),([1,8], -40),([2,6], 4),([2,9], -8),([5,8], -40),([6,9], 4),([7,9], 20),([9,9], 16)]
def c3GroupHessian74_01 : Poly := List.flatten [c3GroupHessian74_01Chunk0]
theorem c3GroupHessian74_01_check : sumFast (c3TensorGroup74.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian74_01 := by kernel_rfl
private def c3GroupHessian74_02Chunk0 : Poly := [([0,0], -40),([0,1], -40),([0,3], 4),([0,5], -80),([0,9], -24),([1,5], -40),([3,6], 4),([3,9], -8),([5,5], -40),([6,9], -4),([7,9], -20),([9,9], -16)]
def c3GroupHessian74_02 : Poly := List.flatten [c3GroupHessian74_02Chunk0]
theorem c3GroupHessian74_02_check : sumFast (c3TensorGroup74.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian74_02 := by kernel_rfl
private def c3GroupHessian74_03Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -16),([0,8], 40),([0,9], -8),([1,4], 40),([1,8], 40),([4,5], 40),([5,8], 40),([6,6], -8),([6,9], -8),([9,9], -16)]
def c3GroupHessian74_03 : Poly := List.flatten [c3GroupHessian74_03Chunk0]
theorem c3GroupHessian74_03_check : sumFast (c3TensorGroup74.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian74_03 := by kernel_rfl
private def c3GroupHessian74_11Chunk0 : Poly := [([0,0], 16),([0,2], -8),([0,7], 40),([0,9], 24),([2,2], 16),([2,7], -40),([2,9], -16),([7,7], 40),([7,9], 40),([8,8], 40),([9,9], 16)]
def c3GroupHessian74_11 : Poly := List.flatten [c3GroupHessian74_11Chunk0]
theorem c3GroupHessian74_11_check : sumFast (c3TensorGroup74.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian74_11 := by kernel_rfl
private def c3GroupHessian74_12Chunk0 : Poly := [([0,0], -20),([0,2], 20),([0,3], -4),([0,7], -60),([0,8], 40),([0,9], -32),([2,3], 16),([2,7], 20),([2,9], 8),([3,7], -20),([3,9], -8),([5,8], 40),([7,7], -40),([7,9], -40),([9,9], -16)]
def c3GroupHessian74_12 : Poly := List.flatten [c3GroupHessian74_12Chunk0]
theorem c3GroupHessian74_12_check : sumFast (c3TensorGroup74.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian74_12 := by kernel_rfl
private def c3GroupHessian74_13Chunk0 : Poly := [([0,0], -4),([0,2], -4),([0,6], -4),([0,8], -40),([0,9], -16),([2,6], -4),([2,9], 8),([4,8], -40),([6,9], -4),([7,9], -20),([8,8], -40),([9,9], -16)]
def c3GroupHessian74_13 : Poly := List.flatten [c3GroupHessian74_13Chunk0]
theorem c3GroupHessian74_13_check : sumFast (c3TensorGroup74.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian74_13 := by kernel_rfl
private def c3GroupHessian74_22Chunk0 : Poly := [([0,0], 80),([0,3], 40),([0,5], 80),([0,7], 80),([0,9], 40),([3,3], 16),([3,7], 40),([3,9], 16),([5,5], 40),([7,7], 40),([7,9], 40),([9,9], 16)]
def c3GroupHessian74_22 : Poly := List.flatten [c3GroupHessian74_22Chunk0]
theorem c3GroupHessian74_22_check : sumFast (c3TensorGroup74.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian74_22 := by kernel_rfl
private def c3GroupHessian74_23Chunk0 : Poly := [([0,0], -40),([0,3], -4),([0,4], -40),([0,5], -40),([0,8], -40),([0,9], 24),([3,6], -4),([3,9], 8),([4,5], -40),([5,8], -40),([6,9], 4),([7,9], 20),([9,9], 16)]
def c3GroupHessian74_23 : Poly := List.flatten [c3GroupHessian74_23Chunk0]
theorem c3GroupHessian74_23_check : sumFast (c3TensorGroup74.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian74_23 := by kernel_rfl
private def c3GroupHessian74_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 16),([0,8], 80),([0,9], 8),([4,4], 40),([4,8], 80),([6,6], 8),([6,9], 8),([8,8], 40),([9,9], 16)]
def c3GroupHessian74_33 : Poly := List.flatten [c3GroupHessian74_33Chunk0]
theorem c3GroupHessian74_33_check : sumFast (c3TensorGroup74.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian74_33 := by kernel_rfl
end D4.Secondary
