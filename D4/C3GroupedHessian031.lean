import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup31_det_check : c3TensorGroup31.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 45)) = true := by kernel_rfl
private def c3GroupHessian31_00Chunk0 : Poly := [([0,0], 16),([0,5], 16),([0,6], 16),([1,1], 40),([1,9], -80),([5,5], 8),([5,6], 8),([6,6], 16),([9,9], 40)]
def c3GroupHessian31_00 : Poly := List.flatten [c3GroupHessian31_00Chunk0]
theorem c3GroupHessian31_00_check : sumFast (c3TensorGroup31.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian31_00 := by kernel_rfl
private def c3GroupHessian31_01Chunk0 : Poly := [([0,0], 8),([0,1], -40),([0,5], 4),([0,6], -8),([0,9], 40),([1,7], -40),([1,8], -40),([1,9], -40),([2,6], -20),([7,9], 40),([8,9], 40),([9,9], 40)]
def c3GroupHessian31_01 : Poly := List.flatten [c3GroupHessian31_01Chunk0]
theorem c3GroupHessian31_01_check : sumFast (c3TensorGroup31.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian31_01 := by kernel_rfl
private def c3GroupHessian31_02Chunk0 : Poly := [([0,0], -8),([0,1], 40),([0,5], -12),([0,6], 8),([0,9], -40),([1,3], 40),([1,7], 40),([1,9], 40),([3,9], -40),([5,5], -8),([5,6], -4),([7,9], -40),([9,9], -40)]
def c3GroupHessian31_02 : Poly := List.flatten [c3GroupHessian31_02Chunk0]
theorem c3GroupHessian31_02_check : sumFast (c3TensorGroup31.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian31_02 := by kernel_rfl
private def c3GroupHessian31_03Chunk0 : Poly := [([0,0], -8),([0,1], 40),([0,5], -4),([0,6], -24),([0,9], -40),([1,4], 40),([1,8], 40),([1,9], 40),([4,9], -40),([5,6], -4),([6,6], -16),([8,9], -40),([9,9], -40)]
def c3GroupHessian31_03 : Poly := List.flatten [c3GroupHessian31_03Chunk0]
theorem c3GroupHessian31_03_check : sumFast (c3TensorGroup31.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian31_03 := by kernel_rfl
private def c3GroupHessian31_11Chunk0 : Poly := [([0,0], 56),([0,2], 40),([0,7], 80),([0,8], 80),([0,9], 80),([2,2], 40),([7,7], 40),([7,8], 80),([7,9], 80),([8,8], 40),([8,9], 80),([9,9], 40)]
def c3GroupHessian31_11 : Poly := List.flatten [c3GroupHessian31_11Chunk0]
theorem c3GroupHessian31_11_check : sumFast (c3TensorGroup31.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian31_11 := by kernel_rfl
private def c3GroupHessian31_12Chunk0 : Poly := [([0,0], -56),([0,2], -20),([0,3], -40),([0,5], -4),([0,7], -80),([0,8], -40),([0,9], -80),([3,7], -40),([3,8], -40),([3,9], -40),([7,7], -40),([7,8], -40),([7,9], -80),([8,9], -40),([9,9], -40)]
def c3GroupHessian31_12 : Poly := List.flatten [c3GroupHessian31_12Chunk0]
theorem c3GroupHessian31_12_check : sumFast (c3TensorGroup31.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian31_12 := by kernel_rfl
private def c3GroupHessian31_13Chunk0 : Poly := [([0,0], -32),([0,2], 20),([0,4], -40),([0,6], 8),([0,7], -40),([0,8], -80),([0,9], -80),([2,6], 20),([4,7], -40),([4,8], -40),([4,9], -40),([7,8], -40),([7,9], -40),([8,8], -40),([8,9], -80),([9,9], -40)]
def c3GroupHessian31_13 : Poly := List.flatten [c3GroupHessian31_13Chunk0]
theorem c3GroupHessian31_13_check : sumFast (c3TensorGroup31.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian31_13 := by kernel_rfl
private def c3GroupHessian31_22Chunk0 : Poly := [([0,0], 56),([0,3], 80),([0,5], 8),([0,7], 80),([0,9], 80),([3,3], 40),([3,7], 80),([3,9], 80),([5,5], 8),([7,7], 40),([7,9], 80),([9,9], 40)]
def c3GroupHessian31_22 : Poly := List.flatten [c3GroupHessian31_22Chunk0]
theorem c3GroupHessian31_22_check : sumFast (c3TensorGroup31.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian31_22 := by kernel_rfl
private def c3GroupHessian31_23Chunk0 : Poly := [([0,0], 32),([0,3], 40),([0,4], 40),([0,5], 4),([0,6], -8),([0,7], 40),([0,8], 40),([0,9], 80),([3,4], 40),([3,8], 40),([3,9], 40),([4,7], 40),([4,9], 40),([5,6], 4),([7,8], 40),([7,9], 40),([8,9], 40),([9,9], 40)]
def c3GroupHessian31_23 : Poly := List.flatten [c3GroupHessian31_23Chunk0]
theorem c3GroupHessian31_23_check : sumFast (c3TensorGroup31.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian31_23 := by kernel_rfl
private def c3GroupHessian31_33Chunk0 : Poly := [([0,0], 56),([0,4], 80),([0,6], 32),([0,8], 80),([0,9], 80),([4,4], 40),([4,8], 80),([4,9], 80),([6,6], 16),([8,8], 40),([8,9], 80),([9,9], 40)]
def c3GroupHessian31_33 : Poly := List.flatten [c3GroupHessian31_33Chunk0]
theorem c3GroupHessian31_33_check : sumFast (c3TensorGroup31.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian31_33 := by kernel_rfl
end D4.Secondary
