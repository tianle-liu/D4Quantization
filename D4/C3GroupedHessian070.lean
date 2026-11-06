import D4.C3GroupedTensorData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace D4.Secondary
open Matrix Analytic Principal Certificate
theorem c3TensorGroup70_det_check : c3TensorGroup70.all (fun t => decide (c3CellDetPoly t = c3CellDetPoly 95)) = true := by kernel_rfl
private def c3GroupHessian70_00Chunk0 : Poly := [([0,0], 48),([0,1], 80),([0,5], 80),([0,6], 16),([1,1], 40),([1,5], 80),([5,5], 40),([6,6], 8),([9,9], 40)]
def c3GroupHessian70_00 : Poly := List.flatten [c3GroupHessian70_00Chunk0]
theorem c3GroupHessian70_00_check : sumFast (c3TensorGroup70.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 0)) = c3GroupHessian70_00 := by kernel_rfl
private def c3GroupHessian70_01Chunk0 : Poly := [([0,0], 8),([0,2], 4),([0,6], 8),([0,8], -40),([0,9], 40),([1,8], -40),([2,6], 4),([2,9], 20),([5,8], -40),([7,9], 40),([9,9], 40)]
def c3GroupHessian70_01 : Poly := List.flatten [c3GroupHessian70_01Chunk0]
theorem c3GroupHessian70_01_check : sumFast (c3TensorGroup70.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 1)) = c3GroupHessian70_01 := by kernel_rfl
private def c3GroupHessian70_02Chunk0 : Poly := [([0,0], -40),([0,1], -40),([0,3], 4),([0,5], -80),([0,9], -40),([1,5], -40),([3,6], 4),([3,9], -20),([5,5], -40),([7,9], -40),([9,9], -40)]
def c3GroupHessian70_02 : Poly := List.flatten [c3GroupHessian70_02Chunk0]
theorem c3GroupHessian70_02_check : sumFast (c3TensorGroup70.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 2)) = c3GroupHessian70_02 := by kernel_rfl
private def c3GroupHessian70_03Chunk0 : Poly := [([0,0], 32),([0,1], 40),([0,4], 40),([0,5], 40),([0,6], -16),([0,8], 40),([1,4], 40),([1,8], 40),([4,5], 40),([5,8], 40),([6,6], -8),([9,9], -40)]
def c3GroupHessian70_03 : Poly := List.flatten [c3GroupHessian70_03Chunk0]
theorem c3GroupHessian70_03_check : sumFast (c3TensorGroup70.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 0 3)) = c3GroupHessian70_03 := by kernel_rfl
private def c3GroupHessian70_11Chunk0 : Poly := [([0,0], 48),([0,2], 48),([0,7], 80),([0,9], 80),([2,2], 16),([2,7], 40),([2,9], 40),([7,7], 40),([7,9], 80),([8,8], 40),([9,9], 40)]
def c3GroupHessian70_11 : Poly := List.flatten [c3GroupHessian70_11Chunk0]
theorem c3GroupHessian70_11_check : sumFast (c3TensorGroup70.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 1)) = c3GroupHessian70_11 := by kernel_rfl
private def c3GroupHessian70_12Chunk0 : Poly := [([0,0], -40),([0,2], -20),([0,3], -16),([0,7], -80),([0,8], 40),([0,9], -80),([2,3], -8),([2,7], -20),([2,9], -20),([3,7], -20),([3,9], -20),([5,8], 40),([7,7], -40),([7,9], -80),([9,9], -40)]
def c3GroupHessian70_12 : Poly := List.flatten [c3GroupHessian70_12Chunk0]
theorem c3GroupHessian70_12_check : sumFast (c3TensorGroup70.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 2)) = c3GroupHessian70_12 := by kernel_rfl
private def c3GroupHessian70_13Chunk0 : Poly := [([0,0], -8),([0,2], -4),([0,6], -8),([0,8], -40),([0,9], -40),([2,6], -4),([2,9], -20),([4,8], -40),([7,9], -40),([8,8], -40),([9,9], -40)]
def c3GroupHessian70_13 : Poly := List.flatten [c3GroupHessian70_13Chunk0]
theorem c3GroupHessian70_13_check : sumFast (c3TensorGroup70.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 1 3)) = c3GroupHessian70_13 := by kernel_rfl
private def c3GroupHessian70_22Chunk0 : Poly := [([0,0], 80),([0,3], 40),([0,5], 80),([0,7], 80),([0,9], 80),([3,3], 16),([3,7], 40),([3,9], 40),([5,5], 40),([7,7], 40),([7,9], 80),([9,9], 40)]
def c3GroupHessian70_22 : Poly := List.flatten [c3GroupHessian70_22Chunk0]
theorem c3GroupHessian70_22_check : sumFast (c3TensorGroup70.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 2)) = c3GroupHessian70_22 := by kernel_rfl
private def c3GroupHessian70_23Chunk0 : Poly := [([0,0], -40),([0,3], -4),([0,4], -40),([0,5], -40),([0,8], -40),([0,9], 40),([3,6], -4),([3,9], 20),([4,5], -40),([5,8], -40),([7,9], 40),([9,9], 40)]
def c3GroupHessian70_23 : Poly := List.flatten [c3GroupHessian70_23Chunk0]
theorem c3GroupHessian70_23_check : sumFast (c3TensorGroup70.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 2 3)) = c3GroupHessian70_23 := by kernel_rfl
private def c3GroupHessian70_33Chunk0 : Poly := [([0,0], 48),([0,4], 80),([0,6], 16),([0,8], 80),([4,4], 40),([4,8], 80),([6,6], 8),([8,8], 40),([9,9], 40)]
def c3GroupHessian70_33 : Poly := List.flatten [c3GroupHessian70_33Chunk0]
theorem c3GroupHessian70_33_check : sumFast (c3TensorGroup70.map (fun t => cellHessianPoly c3VertexCoefficients (c3Cell t) 3 3)) = c3GroupHessian70_33 := by kernel_rfl
end D4.Secondary
